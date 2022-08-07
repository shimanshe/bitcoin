#!/usr/bin/env python3
# Copyright (c) 2016-2020 The Bitcoin Core developers
# Distributed under the MIT software license, see the accompanying
# file COPYING or http://www.opensource.org/licenses/mit-license.php.
"""Test segwit transactions and blocks on P2P network."""
from decimal import Decimal
import math
import random
import struct
import time

from test_framework.blocktools import create_block, create_coinbase, add_witness_commitment, get_witness_script, WITNESS_COMMITMENT_HEADER
from test_framework.key import ECKey
from test_framework.messages import (
    BIP125_SEQUENCE_NUMBER,
    CBlock,
    CBlockHeader,
    CInv,
    COutPoint,
    CTransaction,
    CTxIn,
    CTxInWitness,
    CTxOut,
    CTxWitness,
    # MAX_BLOCK_BASE_SIZE,
    MSG_BLOCK,
    MSG_TX,
    MSG_WITNESS_FLAG,
    MSG_WITNESS_TX,
    MSG_WTX,
    NODE_NETWORK,
    NODE_WITNESS,
    msg_no_witness_block,
    msg_getdata,
    msg_headers,
    msg_inv,
    msg_tx,
    msg_block,
    msg_no_witness_tx,
    ser_uint256,
    ser_vector,
    sha256,
    tx_from_hex,
    from_hex
)
from test_framework.p2p import (
    P2PInterface,
    p2p_lock,
)
from test_framework.script import (
    CScript,
    CScriptNum,
    CScriptOp,
    MAX_SCRIPT_ELEMENT_SIZE,
    OP_0,
    OP_1,
    OP_2,
    OP_3,
    OP_16,
    OP_2DROP,
    OP_CHECKMULTISIG,
    OP_CHECKSIG,
    OP_DUP,
    OP_HASH160,
    OP_EQUALVERIFY,
    OP_DROP,
    OP_ELSE,
    OP_ENDIF,
    OP_IF,
    OP_RETURN,
    OP_TRUE,
    SIGHASH_ALL,
    SIGHASH_ANYONECANPAY,
    SIGHASH_NONE,
    SIGHASH_SINGLE,
    SegwitV0SignatureHash,
    LegacySignatureHash,
    hash160,
)
from test_framework.script_util import (
    key_to_p2wpkh_script,
    keyhash_to_p2pkh_script,
    script_to_p2sh_script,
    script_to_p2wsh_script,
)
from test_framework.test_framework import BitcoinTestFramework
from test_framework.util import (
    assert_equal,
    softfork_active,
    hex_str_to_bytes,
    assert_raises_rpc_error,
)

# The versionbit bit used to signal activation of SegWit
VB_WITNESS_BIT = 1
VB_TOP_BITS = 0x20000000

MAX_SIGOP_COST = 80000

SEGWIT_HEIGHT = 120

class UTXO():
    """Used to keep track of anyone-can-spend outputs that we can use in the tests."""
    def __init__(self, sha256, n, value):
        self.sha256 = sha256
        self.n = n
        self.nValue = value

def sign_p2pk_witness_input(script, tx_to, in_idx, hashtype, value, key):
    """Add signature for a P2PK witness program."""
    tx_hash = SegwitV0SignatureHash(script, tx_to, in_idx, hashtype, value)
    signature = key.sign_ecdsa(tx_hash) + chr(hashtype).encode('latin-1')
    tx_to.wit.vtxinwit[in_idx].scriptWitness.stack = [signature, script]
    tx_to.rehash()

def get_virtual_size(witness_block):
    """Calculate the virtual size of a witness block.

    Virtual size is base + witness/4."""
    base_size = len(witness_block.serialize(with_witness=False))
    total_size = len(witness_block.serialize())
    # the "+3" is so we round up
    vsize = int((3 * base_size + total_size + 3) / 4)
    return vsize

def test_transaction_acceptance(node, p2p, tx, with_witness, accepted, reason=None):
    """Send a transaction to the node and check that it's accepted to the mempool

    - Submit the transaction over the p2p interface
    - use the getrawmempool rpc to check for acceptance."""
    reason = [reason] if reason else []
    with node.assert_debug_log(expected_msgs=reason):
        p2p.send_and_ping(msg_tx(tx) if with_witness else msg_no_witness_tx(tx))
        assert_equal(tx.hash in node.getrawmempool(), accepted)


def test_witness_block(node, p2p, block, accepted, with_witness=True, reason=None):
    """Send a block to the node and check that it's accepted

    - Submit the block over the p2p interface
    - use the getbestblockhash rpc to check for acceptance."""
    reason = [reason] if reason else []
    with node.assert_debug_log(expected_msgs=reason):
        p2p.send_and_ping(msg_block(block) if with_witness else msg_no_witness_block(block))
        assert_equal(node.getbestblockhash() == block.hash, accepted)


class TestP2PConn(P2PInterface):
    def __init__(self, wtxidrelay=False):
        super().__init__(wtxidrelay=wtxidrelay)
        self.getdataset = set()
        self.last_wtxidrelay = []
        self.lastgetdata = []
        self.wtxidrelay = wtxidrelay

    # Don't send getdata message replies to invs automatically.
    # We'll send the getdata messages explicitly in the test logic.
    def on_inv(self, message):
        pass

    def on_getdata(self, message):
        self.lastgetdata = message.inv
        for inv in message.inv:
            self.getdataset.add(inv.hash)

    def on_wtxidrelay(self, message):
        self.last_wtxidrelay.append(message)

    def announce_tx_and_wait_for_getdata(self, tx, success=True, use_wtxid=False):
        if success:
            # sanity check
            assert (self.wtxidrelay and use_wtxid) or (not self.wtxidrelay and not use_wtxid)
        with p2p_lock:
            self.last_message.pop("getdata", None)
        if use_wtxid:
            wtxid = tx.calc_sha256(True)
            self.send_message(msg_inv(inv=[CInv(MSG_WTX, wtxid)]))
        else:
            self.send_message(msg_inv(inv=[CInv(MSG_TX, tx.sha256)]))

        if success:
            if use_wtxid:
                self.wait_for_getdata([wtxid])
            else:
                self.wait_for_getdata([tx.sha256])
        else:
            time.sleep(5)
            assert not self.last_message.get("getdata")

    def announce_block_and_wait_for_getdata(self, block, use_header, timeout=60):
        with p2p_lock:
            self.last_message.pop("getdata", None)
            self.last_message.pop("getheaders", None)
        msg = msg_headers()
        msg.headers = [CBlockHeader(block)]
        if use_header:
            self.send_message(msg)
        else:
            self.send_message(msg_inv(inv=[CInv(MSG_BLOCK, block.sha256)]))
            self.wait_for_getheaders()
            self.send_message(msg)
        self.wait_for_getdata([block.sha256])

    def request_block(self, blockhash, inv_type, timeout=60):
        with p2p_lock:
            self.last_message.pop("block", None)
        self.send_message(msg_getdata(inv=[CInv(inv_type, blockhash)]))
        self.wait_for_block(blockhash, timeout)
        return self.last_message["block"].block

class SegWitTest(BitcoinTestFramework):
    def set_test_params(self):
        self.setup_clean_chain = True
        self.num_nodes = 3
        # This test tests SegWit both pre and post-activation, so use the normal BIP9 activation.
        self.extra_args = [
            ["-acceptnonstdtxn=1", "-segwitheight={}".format(SEGWIT_HEIGHT), "-whitelist=noban@127.0.0.1"],
            ["-acceptnonstdtxn=0", "-segwitheight={}".format(SEGWIT_HEIGHT)],
            ["-acceptnonstdtxn=1", "-segwitheight=-1"],
        ]
        self.supports_cli = False

    def skip_test_if_missing_module(self):
        self.skip_if_no_wallet()

    def setup_network(self):
        self.setup_nodes()
        self.connect_nodes(0, 1)
        self.connect_nodes(0, 2)
        self.sync_all()

    # Helper functions

    def build_next_block(self, version=4):
        """Build a block on top of node0's tip."""
        tip = self.nodes[0].getbestblockhash()
        height = self.nodes[0].getblockcount() + 1
        block_time = self.nodes[0].getblockheader(tip)["mediantime"] + 1
        block = create_block(int(tip, 16), create_coinbase(height), block_time)
        block.nVersion = version
        block.rehash()
        return block

    def update_witness_block_with_transactions(self, block, tx_list, nonce=0):
        """Add list of transactions to block, adds witness commitment, then solves."""
        block.vtx.extend(tx_list)
        add_witness_commitment(block, nonce)
        block.solve()

    def run_test(self):
        # Setup the p2p connections
        # self.test_node sets NODE_WITNESS|NODE_NETWORK
        self.test_node = self.nodes[0].add_p2p_connection(TestP2PConn(), services=NODE_NETWORK | NODE_WITNESS)
        # self.old_node sets only NODE_NETWORK
        self.old_node = self.nodes[0].add_p2p_connection(TestP2PConn(), services=NODE_NETWORK)
        # self.std_node is for testing node1 (fRequireStandard=true)
        self.std_node = self.nodes[1].add_p2p_connection(TestP2PConn(), services=NODE_NETWORK | NODE_WITNESS)
        # self.std_wtx_node is for testing node1 with wtxid relay
        self.std_wtx_node = self.nodes[1].add_p2p_connection(TestP2PConn(wtxidrelay=True), services=NODE_NETWORK | NODE_WITNESS)

        assert self.test_node.nServices & NODE_WITNESS != 0

        # Keep a place to store utxo's that can be used in later tests
        self.utxo = []

        self.log.info("Starting tests before segwit activation")
        self.segwit_active = False

        self.test_non_witness_transaction()
        self.test_v0_outputs_arent_spendable()
        self.test_block_relay()
        self.test_getblocktemplate_before_lockin()
        self.test_unnecessary_witness_before_segwit_activation()
        self.test_witness_tx_relay_before_segwit_activation()
        self.test_standardness_v0()

        self.log.info("Advancing to segwit activation")
        self.advance_to_segwit_active()

        # Segwit status 'active'

        self.test_p2sh_witness()
        # self.test_witness_commitments()
        # self.test_block_malleability()
        # self.test_witness_block_size()
        # self.test_submit_block()
        # self.test_extra_witness_data()
        # self.test_max_witness_push_length()
        # self.test_max_witness_program_length()
        # self.test_witness_input_length()
        # self.test_block_relay()
        # self.test_tx_relay_after_segwit_activation()
        # self.test_standardness_v0()
        # self.test_segwit_versions()
        # self.test_premature_coinbase_witness_spend()
        # self.test_uncompressed_pubkey()
        self.test_signature_version_1()
        # self.test_non_standard_witness_blinding()
        # self.test_non_standard_witness()
        # self.test_upgrade_after_activation()
        # self.test_witness_sigops()
        # self.test_superfluous_witness()
        # self.test_wtxid_relay()

    # Individual tests

    def subtest(func):  # noqa: N805
        """Wraps the subtests for logging and state assertions."""
        def func_wrapper(self, *args, **kwargs):
            self.log.info("Subtest: {} (Segwit active = {})".format(func.__name__, self.segwit_active))
            # Assert segwit status is as expected
            assert_equal(softfork_active(self.nodes[0], 'segwit'), self.segwit_active)
            func(self, *args, **kwargs)
            # Each subtest should leave some utxos for the next subtest
            assert self.utxo
            self.sync_blocks()
            # Assert segwit status is as expected at end of subtest
            assert_equal(softfork_active(self.nodes[0], 'segwit'), self.segwit_active)

        return func_wrapper

    @subtest  # type: ignore
    def test_non_witness_transaction(self):
        """See if sending a regular transaction works, and create a utxo to use in later tests."""
        # Mine a block with an anyone-can-spend coinbase,
        # let it mature, then try to spend it.

        block = self.build_next_block(version=1)
        block.solve()
        self.test_node.send_and_ping(msg_no_witness_block(block))  # make sure the block was processed
        txid = block.vtx[0].sha256

        self.nodes[0].generate(99)  # let the block mature

        # Create a transaction that spends the coinbase
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(txid, 0), b""))
        tx.vout.append(CTxOut(49 * 100000000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE])))
        tx.calc_sha256()

        # Check that serializing it with or without witness is the same
        # This is a sanity check of our testing framework.
        assert_equal(msg_no_witness_tx(tx).serialize(), msg_tx(tx).serialize())

        self.test_node.send_and_ping(msg_tx(tx))  # make sure the block was processed
        assert tx.hash in self.nodes[0].getrawmempool()
        # Save this transaction for later
        self.utxo.append(UTXO(tx.sha256, 0, 49 * 100000000))
        self.nodes[0].generate(1)

    @subtest  # type: ignore
    def test_unnecessary_witness_before_segwit_activation(self):
        """Verify that blocks with witnesses are rejected before activation."""

        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, CScript([OP_TRUE])))
        tx.wit.vtxinwit.append(CTxInWitness())
        tx.wit.vtxinwit[0].scriptWitness.stack = [CScript([CScriptNum(1)])]

        # Verify the hash with witness differs from the txid
        # (otherwise our testing framework must be broken!)
        tx.rehash()
        assert tx.sha256 != tx.calc_sha256(with_witness=True)

        # Construct a segwit-signaling block that includes the transaction.
        block = self.build_next_block(version=(VB_TOP_BITS | (1 << VB_WITNESS_BIT)))
        self.update_witness_block_with_transactions(block, [tx])
        # Sending witness data before activation is not allowed (anti-spam
        # rule).
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False, reason='unexpected-witness')

        # But it should not be permanently marked bad...
        # Resend without witness information.
        self.test_node.send_and_ping(msg_no_witness_block(block))  # make sure the block was processed
        assert_equal(self.nodes[0].getbestblockhash(), block.hash)

        # Update our utxo list; we spent the first entry.
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx.sha256, 0, tx.vout[0].nValue))

    @subtest  # type: ignore
    def test_block_relay(self):
        """Test that block requests to NODE_WITNESS peer are with MSG_WITNESS_FLAG.

        This is true regardless of segwit activation.
        Also test that we don't ask for blocks from unupgraded peers."""

        blocktype = 2 | MSG_WITNESS_FLAG

        # test_node has set NODE_WITNESS, so all getdata requests should be for
        # witness blocks.
        # Test announcing a block via inv results in a getdata, and that
        # announcing a version 4 or random VB block with a header results in a getdata
        block1 = self.build_next_block()
        block1.solve()

        self.test_node.announce_block_and_wait_for_getdata(block1, use_header=False)
        assert self.test_node.last_message["getdata"].inv[0].type == blocktype
        test_witness_block(self.nodes[0], self.test_node, block1, True)

        block2 = self.build_next_block(version=4)
        block2.solve()

        self.test_node.announce_block_and_wait_for_getdata(block2, use_header=True)
        assert self.test_node.last_message["getdata"].inv[0].type == blocktype
        test_witness_block(self.nodes[0], self.test_node, block2, True)

        block3 = self.build_next_block(version=(VB_TOP_BITS | (1 << 15)))
        block3.solve()
        self.test_node.announce_block_and_wait_for_getdata(block3, use_header=True)
        assert self.test_node.last_message["getdata"].inv[0].type == blocktype
        test_witness_block(self.nodes[0], self.test_node, block3, True)

        # Check that we can getdata for witness blocks or regular blocks,
        # and the right thing happens.
        if not self.segwit_active:
            # Before activation, we should be able to request old blocks with
            # or without witness, and they should be the same.
            chain_height = self.nodes[0].getblockcount()
            # Pick 10 random blocks on main chain, and verify that getdata's
            # for MSG_BLOCK, MSG_WITNESS_BLOCK, and rpc getblock() are equal.
            all_heights = list(range(chain_height + 1))
            random.shuffle(all_heights)
            all_heights = all_heights[0:10]
            for height in all_heights:
                block_hash = self.nodes[0].getblockhash(height)
                rpc_block = self.nodes[0].getblock(block_hash, False)
                block_hash = int(block_hash, 16)
                block = self.test_node.request_block(block_hash, 2)
                wit_block = self.test_node.request_block(block_hash, 2 | MSG_WITNESS_FLAG)
                assert_equal(block.serialize(), wit_block.serialize())
                assert_equal(block.serialize(), hex_str_to_bytes(rpc_block))
        else:
            # After activation, witness blocks and non-witness blocks should
            # be different.  Verify rpc getblock() returns witness blocks, while
            # getdata respects the requested type.
            block = self.build_next_block()
            self.update_witness_block_with_transactions(block, [])
            # This gives us a witness commitment.
            assert len(block.vtx[0].wit.vtxinwit) == 1
            assert len(block.vtx[0].wit.vtxinwit[0].scriptWitness.stack) == 1
            test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
            # Now try to retrieve it...
            rpc_block = self.nodes[0].getblock(block.hash, False)
            non_wit_block = self.test_node.request_block(block.sha256, 2)
            wit_block = self.test_node.request_block(block.sha256, 2 | MSG_WITNESS_FLAG)
            assert_equal(wit_block.serialize(), hex_str_to_bytes(rpc_block))
            assert_equal(wit_block.serialize(False), non_wit_block.serialize())
            assert_equal(wit_block.serialize(), block.serialize())

            # Test size, vsize, weight
            rpc_details = self.nodes[0].getblock(block.hash, True)
            assert_equal(rpc_details["size"], len(block.serialize()))
            assert_equal(rpc_details["strippedsize"], len(block.serialize(False)))
            weight = 3 * len(block.serialize(False)) + len(block.serialize())
            assert_equal(rpc_details["weight"], weight)

            # Upgraded node should not ask for blocks from unupgraded
            block4 = self.build_next_block(version=4)
            block4.solve()
            self.old_node.getdataset = set()

            # Blocks can be requested via direct-fetch (immediately upon processing the announcement)
            # or via parallel download (with an indeterminate delay from processing the announcement)
            # so to test that a block is NOT requested, we could guess a time period to sleep for,
            # and then check. We can avoid the sleep() by taking advantage of transaction getdata's
            # being processed after block getdata's, and announce a transaction as well,
            # and then check to see if that particular getdata has been received.
            # Since 0.14, inv's will only be responded to with a getheaders, so send a header
            # to announce this block.
            msg = msg_headers()
            msg.headers = [CBlockHeader(block4)]
            self.old_node.send_message(msg)
            self.old_node.announce_tx_and_wait_for_getdata(block4.vtx[0])
            assert block4.sha256 not in self.old_node.getdataset

    @subtest  # type: ignore
    def test_v0_outputs_arent_spendable(self):
        """Test that v0 outputs aren't spendable before segwit activation.

        ~6 months after segwit activation, the SCRIPT_VERIFY_WITNESS flag was
        backdated so that it applies to all blocks, going back to the genesis
        block.

        Consequently, version 0 witness outputs are never spendable without
        witness, and so can't be spent before segwit activation (the point at which
        blocks are permitted to contain witnesses)."""

        # node2 doesn't need to be connected for this test.
        # (If it's connected, node0 may propagate an invalid block to it over
        # compact blocks and the nodes would have inconsistent tips.)
        self.disconnect_nodes(0, 2)

        # Create two outputs, a p2wsh and p2sh-p2wsh
        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)
        p2sh_script_pubkey = script_to_p2sh_script(script_pubkey)

        value = self.utxo[0].nValue // 3

        tx = CTransaction()
        tx.vin = [CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b'')]
        tx.vout = [CTxOut(value, script_pubkey), CTxOut(value, p2sh_script_pubkey)]
        tx.vout.append(CTxOut(value, CScript([OP_TRUE])))
        tx.rehash()
        txid = tx.sha256

        # Add it to a block
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        # Verify that segwit isn't activated. A block serialized with witness
        # should be rejected prior to activation.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False, with_witness=True, reason='unexpected-witness')
        # Now send the block without witness. It should be accepted
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True, with_witness=False)

        # Now try to spend the outputs. This should fail since SCRIPT_VERIFY_WITNESS is always enabled.
        p2wsh_tx = CTransaction()
        p2wsh_tx.vin = [CTxIn(COutPoint(txid, 0), b'')]
        p2wsh_tx.vout = [CTxOut(value, CScript([OP_TRUE]))]
        p2wsh_tx.wit.vtxinwit.append(CTxInWitness())
        p2wsh_tx.wit.vtxinwit[0].scriptWitness.stack = [CScript([OP_TRUE])]
        p2wsh_tx.rehash()

        p2sh_p2wsh_tx = CTransaction()
        p2sh_p2wsh_tx.vin = [CTxIn(COutPoint(txid, 1), CScript([script_pubkey]))]
        p2sh_p2wsh_tx.vout = [CTxOut(value, CScript([OP_TRUE]))]
        p2sh_p2wsh_tx.wit.vtxinwit.append(CTxInWitness())
        p2sh_p2wsh_tx.wit.vtxinwit[0].scriptWitness.stack = [CScript([OP_TRUE])]
        p2sh_p2wsh_tx.rehash()

        for tx in [p2wsh_tx, p2sh_p2wsh_tx]:

            block = self.build_next_block()
            self.update_witness_block_with_transactions(block, [tx])

            # When the block is serialized with a witness, the block will be rejected because witness
            # data isn't allowed in blocks that don't commit to witness data.
            test_witness_block(self.nodes[0], self.test_node, block, accepted=False, with_witness=True, reason='unexpected-witness')

            # When the block is serialized without witness, validation fails because the transaction is
            # invalid (transactions are always validated with SCRIPT_VERIFY_WITNESS so a segwit v0 transaction
            # without a witness is invalid).
            # Note: The reject reason for this failure could be
            # 'block-validation-failed' (if script check threads > 1) or
            # 'non-mandatory-script-verify-flag (Witness program was passed an
            # empty witness)' (otherwise).
            # TODO: support multiple acceptable reject reasons.
            test_witness_block(self.nodes[0], self.test_node, block, accepted=False, with_witness=False)

        self.connect_nodes(0, 2)

        self.utxo.pop(0)
        self.utxo.append(UTXO(txid, 2, value))

    @subtest  # type: ignore
    def test_getblocktemplate_before_lockin(self):
        txid = int(self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(), 1), 16)

        for node in [self.nodes[0], self.nodes[2]]:
            gbt_results = node.getblocktemplate({"rules": ["segwit"]})
            if node == self.nodes[2]:
                # If this is a non-segwit node, we should not get a witness
                # commitment.
                assert 'default_witness_commitment' not in gbt_results
            else:
                # For segwit-aware nodes, check the witness
                # commitment is correct.
                assert 'default_witness_commitment' in gbt_results
                witness_commitment = gbt_results['default_witness_commitment']

                # Check that default_witness_commitment is present.
                witness_root = CBlock.get_merkle_root([ser_uint256(0),
                                                       ser_uint256(txid)])
                script = get_witness_script(witness_root, 0)
                assert_equal(witness_commitment, script.hex())

        # Clear out the mempool
        self.nodes[0].generate(1)
        self.sync_blocks()

    @subtest  # type: ignore
    def test_witness_tx_relay_before_segwit_activation(self):

        # Generate a transaction that doesn't require a witness, but send it
        # with a witness.  Should be rejected for premature-witness, but should
        # not be added to recently rejected list.
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE])))
        tx.wit.vtxinwit.append(CTxInWitness())
        tx.wit.vtxinwit[0].scriptWitness.stack = [b'a']
        tx.rehash()

        tx_hash = tx.sha256
        tx_value = tx.vout[0].nValue

        # Verify that if a peer doesn't set nServices to include NODE_WITNESS,
        # the getdata is just for the non-witness portion.
        self.old_node.announce_tx_and_wait_for_getdata(tx)
        assert self.old_node.last_message["getdata"].inv[0].type == MSG_TX

        # Since we haven't delivered the tx yet, inv'ing the same tx from
        # a witness transaction ought not result in a getdata.
        self.test_node.announce_tx_and_wait_for_getdata(tx, success=False)

        # Delivering this transaction with witness should fail (no matter who
        # its from)
        assert_equal(len(self.nodes[0].getrawmempool()), 0)
        assert_equal(len(self.nodes[1].getrawmempool()), 0)
        test_transaction_acceptance(self.nodes[0], self.old_node, tx, with_witness=True, accepted=False)
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=True, accepted=False)

        # But eliminating the witness should fix it
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=False, accepted=True)

        # Cleanup: mine the first transaction and update utxo
        self.nodes[0].generate(1)
        assert_equal(len(self.nodes[0].getrawmempool()), 0)

        self.utxo.pop(0)
        self.utxo.append(UTXO(tx_hash, 0, tx_value))

    @subtest  # type: ignore
    def test_standardness_v0(self):
        """Test V0 txout standardness.

        V0 segwit outputs and inputs are always standard.
        V0 segwit inputs may only be mined after activation, but not before."""

        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)
        p2sh_script_pubkey = script_to_p2sh_script(witness_program)

        # First prepare a p2sh output (so that spending it will pass standardness)
        p2sh_tx = CTransaction()
        p2sh_tx.vin = [CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b"")]
        p2sh_tx.vout = [CTxOut(self.utxo[0].nValue - 1000, p2sh_script_pubkey)]
        p2sh_tx.rehash()

        # Mine it on test_node to create the confirmed output.
        test_transaction_acceptance(self.nodes[0], self.test_node, p2sh_tx, with_witness=True, accepted=True)
        self.nodes[0].generate(1)
        self.sync_blocks()

        # Now test standardness of v0 P2WSH outputs.
        # Start by creating a transaction with two outputs.
        tx = CTransaction()
        tx.vin = [CTxIn(COutPoint(p2sh_tx.sha256, 0), CScript([witness_program]))]
        tx.vout = [CTxOut(p2sh_tx.vout[0].nValue - 10000, script_pubkey)]
        tx.vout.append(CTxOut(8000, script_pubkey))  # Might burn this later
        tx.vin[0].nSequence = BIP125_SEQUENCE_NUMBER  # Just to have the option to bump this tx from the mempool
        tx.rehash()

        # This is always accepted, since the mempool policy is to consider segwit as always active
        # and thus allow segwit outputs
        test_transaction_acceptance(self.nodes[1], self.std_node, tx, with_witness=True, accepted=True)

        # Now create something that looks like a P2PKH output. This won't be spendable.
        witness_hash = sha256(witness_program)
        script_pubkey = CScript([OP_0, hash160(witness_hash)])
        tx2 = CTransaction()
        # tx was accepted, so we spend the second output.
        tx2.vin = [CTxIn(COutPoint(tx.sha256, 1), b"")]
        tx2.vout = [CTxOut(7000, script_pubkey)]
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        tx2.rehash()

        test_transaction_acceptance(self.nodes[1], self.std_node, tx2, with_witness=True, accepted=True)

        # Now update self.utxo for later tests.
        tx3 = CTransaction()
        # tx and tx2 were both accepted.  Don't bother trying to reclaim the
        # P2PKH output; just send tx's first output back to an anyone-can-spend.
        self.sync_mempools([self.nodes[0], self.nodes[1]])
        tx3.vin = [CTxIn(COutPoint(tx.sha256, 0), b"")]
        tx3.vout = [CTxOut(tx.vout[0].nValue - 1000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE]))]
        tx3.wit.vtxinwit.append(CTxInWitness())
        tx3.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        tx3.rehash()
        if not self.segwit_active:
            # Just check mempool acceptance, but don't add the transaction to the mempool, since witness is disallowed
            # in blocks and the tx is impossible to mine right now.
            assert_equal(
                self.nodes[0].testmempoolaccept([tx3.serialize_with_witness().hex()]),
                [{
                    'txid': tx3.hash,
                    'wtxid': tx3.getwtxid(),
                    'allowed': True,
                    'vsize': tx3.get_vsize(),
                    'fees': {
                        'base': Decimal('0.00001000'),
                    },
                }],
            )
            # Create the same output as tx3, but by replacing tx
            tx3_out = tx3.vout[0]
            tx3 = tx
            tx3.vout = [tx3_out]
            tx3.rehash()
            assert_equal(
                self.nodes[0].testmempoolaccept([tx3.serialize_with_witness().hex()]),
                [{
                    'txid': tx3.hash,
                    'wtxid': tx3.getwtxid(),
                    'allowed': True,
                    'vsize': tx3.get_vsize(),
                    'fees': {
                        'base': Decimal('0.00011000'),
                    },
                }],
            )
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, with_witness=True, accepted=True)

        self.nodes[0].generate(1)
        self.sync_blocks()
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx3.sha256, 0, tx3.vout[0].nValue))
        assert_equal(len(self.nodes[1].getrawmempool()), 0)

    @subtest  # type: ignore
    def advance_to_segwit_active(self):
        """Mine enough blocks to activate segwit."""
        assert not softfork_active(self.nodes[0], 'segwit')
        height = self.nodes[0].getblockcount()
        self.nodes[0].generate(SEGWIT_HEIGHT - height - 2)
        assert not softfork_active(self.nodes[0], 'segwit')
        self.nodes[0].generate(1)
        assert softfork_active(self.nodes[0], 'segwit')
        self.segwit_active = True

    @subtest  # type: ignore
    def test_p2sh_witness(self):
        """Test P2SH wrapped witness programs."""

        # Prepare the p2sh-wrapped witness output
        witness_program = CScript([OP_DROP, OP_TRUE])
        p2wsh_pubkey = script_to_p2wsh_script(witness_program)
        script_pubkey = script_to_p2sh_script(p2wsh_pubkey)
        script_sig = CScript([p2wsh_pubkey])  # a push of the redeem script

        # Fund the P2SH output
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()

        # Verify mempool acceptance and block validity
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=False, accepted=True)
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True, with_witness=True)
        self.sync_blocks()

        # Now test attempts to spend the output.
        spend_tx = CTransaction()
        spend_tx.vin.append(CTxIn(COutPoint(tx.sha256, 0), script_sig))
        spend_tx.vout.append(CTxOut(tx.vout[0].nValue - 1000, CScript([OP_TRUE])))
        spend_tx.rehash()

        # This transaction should not be accepted into the mempool pre- or
        # post-segwit.  Mempool acceptance will use SCRIPT_VERIFY_WITNESS which
        # will require a witness to spend a witness program regardless of
        # segwit activation.  Note that older bitcoind's that are not
        # segwit-aware would also reject this for failing CLEANSTACK.
        with self.nodes[0].assert_debug_log(
                expected_msgs=(spend_tx.hash, 'was not accepted: non-mandatory-script-verify-flag (Witness program was passed an empty witness)')):
            test_transaction_acceptance(self.nodes[0], self.test_node, spend_tx, with_witness=False, accepted=False)

        # Try to put the witness script in the scriptSig, should also fail.
        spend_tx.vin[0].scriptSig = CScript([p2wsh_pubkey, b'a'])
        spend_tx.rehash()
        with self.nodes[0].assert_debug_log(
                expected_msgs=(spend_tx.hash, 'was not accepted: mandatory-script-verify-flag-failed (Script evaluated without error but finished with a false/empty top stack element)')):
            test_transaction_acceptance(self.nodes[0], self.test_node, spend_tx, with_witness=False, accepted=False)

        # Now put the witness script in the witness, should succeed after
        # segwit activates.
        spend_tx.vin[0].scriptSig = script_sig
        spend_tx.rehash()
        spend_tx.wit.vtxinwit.append(CTxInWitness())
        spend_tx.wit.vtxinwit[0].scriptWitness.stack = [b'a', witness_program]

        # Verify mempool acceptance
        test_transaction_acceptance(self.nodes[0], self.test_node, spend_tx, with_witness=True, accepted=True)
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [spend_tx])

        # If we're after activation, then sending this with witnesses should be valid.
        # This no longer works before activation, because SCRIPT_VERIFY_WITNESS
        # is always set.
        # TODO: rewrite this test to make clear that it only works after activation.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Update self.utxo
        self.utxo.pop(0)
        self.utxo.append(UTXO(spend_tx.sha256, 0, spend_tx.vout[0].nValue))

    @subtest  # type: ignore
    def test_witness_commitments(self):
        """Test witness commitments.

        This test can only be run after segwit has activated."""

        # First try a correct witness commitment.
        block = self.build_next_block()
        add_witness_commitment(block)
        block.solve()

        # Test the test -- witness serialization should be different
        assert msg_block(block).serialize() != msg_no_witness_block(block).serialize()

        # This empty block should be valid.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Try to tweak the nonce
        block_2 = self.build_next_block()
        add_witness_commitment(block_2, nonce=28)
        block_2.solve()

        # The commitment should have changed!
        assert block_2.vtx[0].vout[-1] != block.vtx[0].vout[-1]

        # This should also be valid.
        test_witness_block(self.nodes[0], self.test_node, block_2, accepted=True)

        # Now test commitments with actual transactions
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))

        # Let's construct a witness program
        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()

        # tx2 will spend tx1, and send back to a regular anyone-can-spend address
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, witness_program))
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        tx2.rehash()

        block_3 = self.build_next_block()
        self.update_witness_block_with_transactions(block_3, [tx, tx2], nonce=1)
        # Add an extra OP_RETURN output that matches the witness commitment template,
        # even though it has extra data after the incorrect commitment.
        # This block should fail.
        block_3.vtx[0].vout.append(CTxOut(0, CScript([OP_RETURN, WITNESS_COMMITMENT_HEADER + ser_uint256(2), 10])))
        block_3.vtx[0].rehash()
        block_3.hashMerkleRoot = block_3.calc_merkle_root()
        block_3.rehash()
        block_3.solve()

        test_witness_block(self.nodes[0], self.test_node, block_3, accepted=False)

        # Add a different commitment with different nonce, but in the
        # right location, and with some funds burned(!).
        # This should succeed (nValue shouldn't affect finding the
        # witness commitment).
        add_witness_commitment(block_3, nonce=0)
        block_3.vtx[0].vout[0].nValue -= 1
        block_3.vtx[0].vout[-1].nValue += 1
        block_3.vtx[0].rehash()
        block_3.hashMerkleRoot = block_3.calc_merkle_root()
        block_3.rehash()
        assert len(block_3.vtx[0].vout) == 4  # 3 OP_returns
        block_3.solve()
        test_witness_block(self.nodes[0], self.test_node, block_3, accepted=True)

        # Finally test that a block with no witness transactions can
        # omit the commitment.
        block_4 = self.build_next_block()
        tx3 = CTransaction()
        tx3.vin.append(CTxIn(COutPoint(tx2.sha256, 0), b""))
        tx3.vout.append(CTxOut(tx.vout[0].nValue - 1000, witness_program))
        tx3.rehash()
        block_4.vtx.append(tx3)
        block_4.hashMerkleRoot = block_4.calc_merkle_root()
        block_4.solve()
        test_witness_block(self.nodes[0], self.test_node, block_4, with_witness=False, accepted=True)

        # Update available utxo's for use in later test.
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx3.sha256, 0, tx3.vout[0].nValue))

    @subtest  # type: ignore
    def test_block_malleability(self):

        # Make sure that a block that has too big a virtual size
        # because of a too-large coinbase witness is not permanently
        # marked bad.
        block = self.build_next_block()
        add_witness_commitment(block)
        block.solve()

        block.vtx[0].wit.vtxinwit[0].scriptWitness.stack.append(b'a' * 5000000)
        assert get_virtual_size(block) > MAX_BLOCK_BASE_SIZE

        # We can't send over the p2p network, because this is too big to relay
        # TODO: repeat this test with a block that can be relayed
        assert_equal('bad-witness-nonce-size', self.nodes[0].submitblock(block.serialize().hex()))

        assert self.nodes[0].getbestblockhash() != block.hash

        block.vtx[0].wit.vtxinwit[0].scriptWitness.stack.pop()
        assert get_virtual_size(block) < MAX_BLOCK_BASE_SIZE
        assert_equal(None, self.nodes[0].submitblock(block.serialize().hex()))

        assert self.nodes[0].getbestblockhash() == block.hash

        # Now make sure that malleating the witness reserved value doesn't
        # result in a block permanently marked bad.
        block = self.build_next_block()
        add_witness_commitment(block)
        block.solve()

        # Change the nonce -- should not cause the block to be permanently
        # failed
        block.vtx[0].wit.vtxinwit[0].scriptWitness.stack = [ser_uint256(1)]
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Changing the witness reserved value doesn't change the block hash
        block.vtx[0].wit.vtxinwit[0].scriptWitness.stack = [ser_uint256(0)]
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

    @subtest  # type: ignore
    def test_witness_block_size(self):
        # TODO: Test that non-witness carrying blocks can't exceed 1MB
        # Skipping this test for now; this is covered in p2p-fullblocktest.py

        # Test that witness-bearing blocks are limited at ceil(base + wit/4) <= 1MB.
        block = self.build_next_block()

        assert len(self.utxo) > 0

        # Create a P2WSH transaction.
        # The witness program will be a bunch of OP_2DROP's, followed by OP_TRUE.
        # This should give us plenty of room to tweak the spending tx's
        # virtual size.
        NUM_DROPS = 200  # 201 max ops per script!
        NUM_OUTPUTS = 50

        witness_program = CScript([OP_2DROP] * NUM_DROPS + [OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)

        prevout = COutPoint(self.utxo[0].sha256, self.utxo[0].n)
        value = self.utxo[0].nValue

        parent_tx = CTransaction()
        parent_tx.vin.append(CTxIn(prevout, b""))
        child_value = int(value / NUM_OUTPUTS)
        for _ in range(NUM_OUTPUTS):
            parent_tx.vout.append(CTxOut(child_value, script_pubkey))
        parent_tx.vout[0].nValue -= 50000
        assert parent_tx.vout[0].nValue > 0
        parent_tx.rehash()

        child_tx = CTransaction()
        for i in range(NUM_OUTPUTS):
            child_tx.vin.append(CTxIn(COutPoint(parent_tx.sha256, i), b""))
        child_tx.vout = [CTxOut(value - 100000, CScript([OP_TRUE]))]
        for _ in range(NUM_OUTPUTS):
            child_tx.wit.vtxinwit.append(CTxInWitness())
            child_tx.wit.vtxinwit[-1].scriptWitness.stack = [b'a' * 195] * (2 * NUM_DROPS) + [witness_program]
        child_tx.rehash()
        self.update_witness_block_with_transactions(block, [parent_tx, child_tx])

        vsize = get_virtual_size(block)
        additional_bytes = (MAX_BLOCK_BASE_SIZE - vsize) * 4
        i = 0
        while additional_bytes > 0:
            # Add some more bytes to each input until we hit MAX_BLOCK_BASE_SIZE+1
            extra_bytes = min(additional_bytes + 1, 55)
            block.vtx[-1].wit.vtxinwit[int(i / (2 * NUM_DROPS))].scriptWitness.stack[i % (2 * NUM_DROPS)] = b'a' * (195 + extra_bytes)
            additional_bytes -= extra_bytes
            i += 1

        block.vtx[0].vout.pop()  # Remove old commitment
        add_witness_commitment(block)
        block.solve()
        vsize = get_virtual_size(block)
        assert_equal(vsize, MAX_BLOCK_BASE_SIZE + 1)
        # Make sure that our test case would exceed the old max-network-message
        # limit
        assert len(block.serialize()) > 2 * 1024 * 1024

        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now resize the second transaction to make the block fit.
        cur_length = len(block.vtx[-1].wit.vtxinwit[0].scriptWitness.stack[0])
        block.vtx[-1].wit.vtxinwit[0].scriptWitness.stack[0] = b'a' * (cur_length - 1)
        block.vtx[0].vout.pop()
        add_witness_commitment(block)
        block.solve()
        assert get_virtual_size(block) == MAX_BLOCK_BASE_SIZE

        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Update available utxo's
        self.utxo.pop(0)
        self.utxo.append(UTXO(block.vtx[-1].sha256, 0, block.vtx[-1].vout[0].nValue))

    @subtest  # type: ignore
    def test_submit_block(self):
        """Test that submitblock adds the nonce automatically when possible."""
        block = self.build_next_block()

        # Try using a custom nonce and then don't supply it.
        # This shouldn't possibly work.
        add_witness_commitment(block, nonce=1)
        block.vtx[0].wit = CTxWitness()  # drop the nonce
        block.solve()
        assert_equal('bad-witness-merkle-match', self.nodes[0].submitblock(block.serialize().hex()))
        assert self.nodes[0].getbestblockhash() != block.hash

        # Now redo commitment with the standard nonce, but let bitcoind fill it in.
        add_witness_commitment(block, nonce=0)
        block.vtx[0].wit = CTxWitness()
        block.solve()
        assert_equal(None, self.nodes[0].submitblock(block.serialize().hex()))
        assert_equal(self.nodes[0].getbestblockhash(), block.hash)

        # This time, add a tx with non-empty witness, but don't supply
        # the commitment.
        block_2 = self.build_next_block()

        add_witness_commitment(block_2)

        block_2.solve()

        # Drop commitment and nonce -- submitblock should not fill in.
        block_2.vtx[0].vout.pop()
        block_2.vtx[0].wit = CTxWitness()

        assert_equal('bad-txnmrklroot', self.nodes[0].submitblock(block_2.serialize().hex()))
        # Tip should not advance!
        assert self.nodes[0].getbestblockhash() != block_2.hash

    @subtest  # type: ignore
    def test_extra_witness_data(self):
        """Test extra witness data in a transaction."""

        block = self.build_next_block()

        witness_program = CScript([OP_DROP, OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)

        # First try extra witness data on a tx that doesn't require a witness
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 2000, script_pubkey))
        tx.vout.append(CTxOut(1000, CScript([OP_TRUE])))  # non-witness output
        tx.wit.vtxinwit.append(CTxInWitness())
        tx.wit.vtxinwit[0].scriptWitness.stack = [CScript([])]
        tx.rehash()
        self.update_witness_block_with_transactions(block, [tx])

        # Extra witness data should not be allowed.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Try extra signature data.  Ok if we're not spending a witness output.
        block.vtx[1].wit.vtxinwit = []
        block.vtx[1].vin[0].scriptSig = CScript([OP_0])
        block.vtx[1].rehash()
        add_witness_commitment(block)
        block.solve()

        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Now try extra witness/signature data on an input that DOES require a
        # witness
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))  # witness output
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 1), b""))  # non-witness
        tx2.vout.append(CTxOut(tx.vout[0].nValue, CScript([OP_TRUE])))
        tx2.wit.vtxinwit.extend([CTxInWitness(), CTxInWitness()])
        tx2.wit.vtxinwit[0].scriptWitness.stack = [CScript([CScriptNum(1)]), CScript([CScriptNum(1)]), witness_program]
        tx2.wit.vtxinwit[1].scriptWitness.stack = [CScript([OP_TRUE])]

        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx2])

        # This has extra witness data, so it should fail.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now get rid of the extra witness, but add extra scriptSig data
        tx2.vin[0].scriptSig = CScript([OP_TRUE])
        tx2.vin[1].scriptSig = CScript([OP_TRUE])
        tx2.wit.vtxinwit[0].scriptWitness.stack.pop(0)
        tx2.wit.vtxinwit[1].scriptWitness.stack = []
        tx2.rehash()
        add_witness_commitment(block)
        block.solve()

        # This has extra signature data for a witness input, so it should fail.
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now get rid of the extra scriptsig on the witness input, and verify
        # success (even with extra scriptsig data in the non-witness input)
        tx2.vin[0].scriptSig = b""
        tx2.rehash()
        add_witness_commitment(block)
        block.solve()

        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Update utxo for later tests
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

    @subtest  # type: ignore
    def test_max_witness_push_length(self):
        """Test that witness stack can only allow up to 520 byte pushes."""

        block = self.build_next_block()

        witness_program = CScript([OP_DROP, OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)

        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()

        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, CScript([OP_TRUE])))
        tx2.wit.vtxinwit.append(CTxInWitness())
        # First try a 521-byte stack element
        tx2.wit.vtxinwit[0].scriptWitness.stack = [b'a' * (MAX_SCRIPT_ELEMENT_SIZE + 1), witness_program]
        tx2.rehash()

        self.update_witness_block_with_transactions(block, [tx, tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now reduce the length of the stack element
        tx2.wit.vtxinwit[0].scriptWitness.stack[0] = b'a' * (MAX_SCRIPT_ELEMENT_SIZE)

        add_witness_commitment(block)
        block.solve()
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Update the utxo for later tests
        self.utxo.pop()
        self.utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

    @subtest  # type: ignore
    def test_max_witness_program_length(self):
        """Test that witness outputs greater than 10kB can't be spent."""

        MAX_PROGRAM_LENGTH = 10000

        # This program is 19 max pushes (9937 bytes), then 64 more opcode-bytes.
        long_witness_program = CScript([b'a' * MAX_SCRIPT_ELEMENT_SIZE] * 19 + [OP_DROP] * 63 + [OP_TRUE])
        assert len(long_witness_program) == MAX_PROGRAM_LENGTH + 1
        long_script_pubkey = script_to_p2wsh_script(long_witness_program)

        block = self.build_next_block()

        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, long_script_pubkey))
        tx.rehash()

        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, CScript([OP_TRUE])))
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [b'a'] * 44 + [long_witness_program]
        tx2.rehash()

        self.update_witness_block_with_transactions(block, [tx, tx2])

        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Try again with one less byte in the witness program
        witness_program = CScript([b'a' * MAX_SCRIPT_ELEMENT_SIZE] * 19 + [OP_DROP] * 62 + [OP_TRUE])
        assert len(witness_program) == MAX_PROGRAM_LENGTH
        script_pubkey = script_to_p2wsh_script(witness_program)

        tx.vout[0] = CTxOut(tx.vout[0].nValue, script_pubkey)
        tx.rehash()
        tx2.vin[0].prevout.hash = tx.sha256
        tx2.wit.vtxinwit[0].scriptWitness.stack = [b'a'] * 43 + [witness_program]
        tx2.rehash()
        block.vtx = [block.vtx[0]]
        self.update_witness_block_with_transactions(block, [tx, tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        self.utxo.pop()
        self.utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

    @subtest  # type: ignore
    def test_witness_input_length(self):
        """Test that vin length must match vtxinwit length."""

        witness_program = CScript([OP_DROP, OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)

        # Create a transaction that splits our utxo into many outputs
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        value = self.utxo[0].nValue
        for _ in range(10):
            tx.vout.append(CTxOut(int(value / 10), script_pubkey))
        tx.vout[0].nValue -= 1000
        assert tx.vout[0].nValue >= 0

        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Try various ways to spend tx that should all break.
        # This "broken" transaction serializer will not normalize
        # the length of vtxinwit.
        class BrokenCTransaction(CTransaction):
            def serialize_with_witness(self):
                flags = 0
                if not self.wit.is_null():
                    flags |= 1
                r = b""
                r += struct.pack("<i", self.nVersion)
                if flags:
                    dummy = []
                    r += ser_vector(dummy)
                    r += struct.pack("<B", flags)
                r += ser_vector(self.vin)
                r += ser_vector(self.vout)
                if flags & 1:
                    r += self.wit.serialize()
                r += struct.pack("<I", self.nLockTime)
                return r

        tx2 = BrokenCTransaction()
        for i in range(10):
            tx2.vin.append(CTxIn(COutPoint(tx.sha256, i), b""))
        tx2.vout.append(CTxOut(value - 3000, CScript([OP_TRUE])))

        # First try using a too long vtxinwit
        for i in range(11):
            tx2.wit.vtxinwit.append(CTxInWitness())
            tx2.wit.vtxinwit[i].scriptWitness.stack = [b'a', witness_program]

        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now try using a too short vtxinwit
        tx2.wit.vtxinwit.pop()
        tx2.wit.vtxinwit.pop()

        block.vtx = [block.vtx[0]]
        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Now make one of the intermediate witnesses be incorrect
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[-1].scriptWitness.stack = [b'a', witness_program]
        tx2.wit.vtxinwit[5].scriptWitness.stack = [witness_program]

        block.vtx = [block.vtx[0]]
        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Fix the broken witness and the block should be accepted.
        tx2.wit.vtxinwit[5].scriptWitness.stack = [b'a', witness_program]
        block.vtx = [block.vtx[0]]
        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        self.utxo.pop()
        self.utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

    @subtest  # type: ignore
    def test_tx_relay_after_segwit_activation(self):
        """Test transaction relay after segwit activation.

        After segwit activates, verify that mempool:
        - rejects transactions with unnecessary/extra witnesses
        - accepts transactions with valid witnesses
        and that witness transactions are relayed to non-upgraded peers."""

        # Generate a transaction that doesn't require a witness, but send it
        # with a witness.  Should be rejected because we can't use a witness
        # when spending a non-witness output.
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE])))
        tx.wit.vtxinwit.append(CTxInWitness())
        tx.wit.vtxinwit[0].scriptWitness.stack = [b'a']
        tx.rehash()

        tx_hash = tx.sha256

        # Verify that unnecessary witnesses are rejected.
        self.test_node.announce_tx_and_wait_for_getdata(tx)
        assert_equal(len(self.nodes[0].getrawmempool()), 0)
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=True, accepted=False)

        # Verify that removing the witness succeeds.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=False, accepted=True)

        # Now try to add extra witness data to a valid witness tx.
        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx_hash, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, script_pubkey))
        tx2.rehash()

        tx3 = CTransaction()
        tx3.vin.append(CTxIn(COutPoint(tx2.sha256, 0), b""))
        tx3.wit.vtxinwit.append(CTxInWitness())

        # Add too-large for IsStandard witness and check that it does not enter reject filter
        p2sh_program = CScript([OP_TRUE])
        witness_program2 = CScript([b'a' * 400000])
        tx3.vout.append(CTxOut(tx2.vout[0].nValue - 1000, script_to_p2sh_script(p2sh_program)))
        tx3.wit.vtxinwit[0].scriptWitness.stack = [witness_program2]
        tx3.rehash()

        # Node will not be blinded to the transaction, requesting it any number of times
        # if it is being announced via txid relay.
        # Node will be blinded to the transaction via wtxid, however.
        self.std_node.announce_tx_and_wait_for_getdata(tx3)
        self.std_wtx_node.announce_tx_and_wait_for_getdata(tx3, use_wtxid=True)
        test_transaction_acceptance(self.nodes[1], self.std_node, tx3, True, False, 'tx-size')
        self.std_node.announce_tx_and_wait_for_getdata(tx3)
        self.std_wtx_node.announce_tx_and_wait_for_getdata(tx3, use_wtxid=True, success=False)

        # Remove witness stuffing, instead add extra witness push on stack
        tx3.vout[0] = CTxOut(tx2.vout[0].nValue - 1000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE]))
        tx3.wit.vtxinwit[0].scriptWitness.stack = [CScript([CScriptNum(1)]), witness_program]
        tx3.rehash()

        test_transaction_acceptance(self.nodes[0], self.test_node, tx2, with_witness=True, accepted=True)
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, with_witness=True, accepted=False)

        # Get rid of the extra witness, and verify acceptance.
        tx3.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        # Also check that old_node gets a tx announcement, even though this is
        # a witness transaction.
        self.old_node.wait_for_inv([CInv(MSG_TX, tx2.sha256)])  # wait until tx2 was inv'ed
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, with_witness=True, accepted=True)
        self.old_node.wait_for_inv([CInv(MSG_TX, tx3.sha256)])

        # Test that getrawtransaction returns correct witness information
        # hash, size, vsize
        raw_tx = self.nodes[0].getrawtransaction(tx3.hash, 1)
        assert_equal(int(raw_tx["hash"], 16), tx3.calc_sha256(True))
        assert_equal(raw_tx["size"], len(tx3.serialize_with_witness()))
        weight = len(tx3.serialize_with_witness()) + 3 * len(tx3.serialize_without_witness())
        vsize = math.ceil(weight / 4)
        assert_equal(raw_tx["vsize"], vsize)
        assert_equal(raw_tx["weight"], weight)
        assert_equal(len(raw_tx["vin"][0]["txinwitness"]), 1)
        assert_equal(raw_tx["vin"][0]["txinwitness"][0], witness_program.hex())
        assert vsize != raw_tx["size"]

        # Cleanup: mine the transactions and update utxo for next test
        self.nodes[0].generate(1)
        assert_equal(len(self.nodes[0].getrawmempool()), 0)

        self.utxo.pop(0)
        self.utxo.append(UTXO(tx3.sha256, 0, tx3.vout[0].nValue))

    @subtest  # type: ignore
    def test_segwit_versions(self):
        """Test validity of future segwit version transactions.

        Future segwit versions are non-standard to spend, but valid in blocks.
        Sending to future segwit versions is always allowed.
        Can run this before and after segwit activation."""

        NUM_SEGWIT_VERSIONS = 17  # will test OP_0, OP1, ..., OP_16
        if len(self.utxo) < NUM_SEGWIT_VERSIONS:
            tx = CTransaction()
            tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
            split_value = (self.utxo[0].nValue - 4000) // NUM_SEGWIT_VERSIONS
            for _ in range(NUM_SEGWIT_VERSIONS):
                tx.vout.append(CTxOut(split_value, CScript([OP_TRUE])))
            tx.rehash()
            block = self.build_next_block()
            self.update_witness_block_with_transactions(block, [tx])
            test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
            self.utxo.pop(0)
            for i in range(NUM_SEGWIT_VERSIONS):
                self.utxo.append(UTXO(tx.sha256, i, split_value))

        self.sync_blocks()
        temp_utxo = []
        tx = CTransaction()
        witness_program = CScript([OP_TRUE])
        witness_hash = sha256(witness_program)
        assert_equal(len(self.nodes[1].getrawmempool()), 0)
        for version in list(range(OP_1, OP_16 + 1)) + [OP_0]:
            # First try to spend to a future version segwit script_pubkey.
            if version == OP_1:
                # Don't use 32-byte v1 witness (used by Taproot; see BIP 341)
                script_pubkey = CScript([CScriptOp(version), witness_hash + b'\x00'])
            else:
                script_pubkey = CScript([CScriptOp(version), witness_hash])
            tx.vin = [CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b"")]
            tx.vout = [CTxOut(self.utxo[0].nValue - 1000, script_pubkey)]
            tx.rehash()
            test_transaction_acceptance(self.nodes[1], self.std_node, tx, with_witness=True, accepted=False)
            test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=True, accepted=True)
            self.utxo.pop(0)
            temp_utxo.append(UTXO(tx.sha256, 0, tx.vout[0].nValue))

        self.nodes[0].generate(1)  # Mine all the transactions
        self.sync_blocks()
        assert len(self.nodes[0].getrawmempool()) == 0

        # Finally, verify that version 0 -> version 2 transactions
        # are standard
        script_pubkey = CScript([CScriptOp(OP_2), witness_hash])
        tx2 = CTransaction()
        tx2.vin = [CTxIn(COutPoint(tx.sha256, 0), b"")]
        tx2.vout = [CTxOut(tx.vout[0].nValue - 1000, script_pubkey)]
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        tx2.rehash()
        # Gets accepted to both policy-enforcing nodes and others.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx2, with_witness=True, accepted=True)
        test_transaction_acceptance(self.nodes[1], self.std_node, tx2, with_witness=True, accepted=True)
        temp_utxo.pop()  # last entry in temp_utxo was the output we just spent
        temp_utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

        # Spend everything in temp_utxo into an segwit v1 output.
        tx3 = CTransaction()
        total_value = 0
        for i in temp_utxo:
            tx3.vin.append(CTxIn(COutPoint(i.sha256, i.n), b""))
            tx3.wit.vtxinwit.append(CTxInWitness())
            total_value += i.nValue
        tx3.wit.vtxinwit[-1].scriptWitness.stack = [witness_program]
        tx3.vout.append(CTxOut(total_value - 1000, script_pubkey))
        tx3.rehash()

        # First we test this transaction against fRequireStandard=true node
        # making sure the txid is added to the reject filter
        self.std_node.announce_tx_and_wait_for_getdata(tx3)
        test_transaction_acceptance(self.nodes[1], self.std_node, tx3, with_witness=True, accepted=False, reason="bad-txns-nonstandard-inputs")
        # Now the node will no longer ask for getdata of this transaction when advertised by same txid
        self.std_node.announce_tx_and_wait_for_getdata(tx3, success=False)

        # Spending a higher version witness output is not allowed by policy,
        # even with fRequireStandard=false.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, with_witness=True, accepted=False, reason="reserved for soft-fork upgrades")

        # Building a block with the transaction must be valid, however.
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx2, tx3])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
        self.sync_blocks()

        # Add utxo to our list
        self.utxo.append(UTXO(tx3.sha256, 0, tx3.vout[0].nValue))

    @subtest  # type: ignore
    def test_premature_coinbase_witness_spend(self):

        block = self.build_next_block()
        # Change the output of the block to be a witness output.
        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)
        block.vtx[0].vout[0].scriptPubKey = script_pubkey
        # This next line will rehash the coinbase and update the merkle
        # root, and solve.
        self.update_witness_block_with_transactions(block, [])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        spend_tx = CTransaction()
        spend_tx.vin = [CTxIn(COutPoint(block.vtx[0].sha256, 0), b"")]
        spend_tx.vout = [CTxOut(block.vtx[0].vout[0].nValue, witness_program)]
        spend_tx.wit.vtxinwit.append(CTxInWitness())
        spend_tx.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        spend_tx.rehash()

        # Now test a premature spend.
        self.nodes[0].generate(98)
        self.sync_blocks()
        block2 = self.build_next_block()
        self.update_witness_block_with_transactions(block2, [spend_tx])
        test_witness_block(self.nodes[0], self.test_node, block2, accepted=False)

        # Advancing one more block should allow the spend.
        self.nodes[0].generate(1)
        block2 = self.build_next_block()
        self.update_witness_block_with_transactions(block2, [spend_tx])
        test_witness_block(self.nodes[0], self.test_node, block2, accepted=True)
        self.sync_blocks()

    @subtest  # type: ignore
    def test_uncompressed_pubkey(self):
        """Test uncompressed pubkey validity in segwit transactions.

        Uncompressed pubkeys are no longer supported in default relay policy,
        but (for now) are still valid in blocks."""

        # Segwit transactions using uncompressed pubkeys are not accepted
        # under default policy, but should still pass consensus.
        key = ECKey()
        key.generate(False)
        pubkey = key.get_pubkey().get_bytes()
        assert_equal(len(pubkey), 65)  # This should be an uncompressed pubkey

        utxo = self.utxo.pop(0)

        # Test 1: P2WPKH
        # First create a P2WPKH output that uses an uncompressed pubkey
        pubkeyhash = hash160(pubkey)
        script_pkh = key_to_p2wpkh_script(pubkey)
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(utxo.sha256, utxo.n), b""))
        tx.vout.append(CTxOut(utxo.nValue - 1000, script_pkh))
        tx.rehash()

        # Confirm it in a block.
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Now try to spend it. Send it to a P2WSH output, which we'll
        # use in the next test.
        witness_program = CScript([pubkey, CScriptOp(OP_CHECKSIG)])
        script_wsh = script_to_p2wsh_script(witness_program)

        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, script_wsh))
        script = keyhash_to_p2pkh_script(pubkeyhash)
        sig_hash = SegwitV0SignatureHash(script, tx2, 0, SIGHASH_ALL, tx.vout[0].nValue)
        signature = key.sign_ecdsa(sig_hash) + b'\x01'  # 0x1 is SIGHASH_ALL
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [signature, pubkey]
        tx2.rehash()

        # Should fail policy test.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx2, True, False, 'non-mandatory-script-verify-flag (Using non-compressed keys in segwit)')
        # But passes consensus.
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Test 2: P2WSH
        # Try to spend the P2WSH output created in last test.
        # Send it to a P2SH(P2WSH) output, which we'll use in the next test.
        script_p2sh = script_to_p2sh_script(script_wsh)
        script_sig = CScript([script_wsh])

        tx3 = CTransaction()
        tx3.vin.append(CTxIn(COutPoint(tx2.sha256, 0), b""))
        tx3.vout.append(CTxOut(tx2.vout[0].nValue - 1000, script_p2sh))
        tx3.wit.vtxinwit.append(CTxInWitness())
        sign_p2pk_witness_input(witness_program, tx3, 0, SIGHASH_ALL, tx2.vout[0].nValue, key)

        # Should fail policy test.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, True, False, 'non-mandatory-script-verify-flag (Using non-compressed keys in segwit)')
        # But passes consensus.
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx3])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Test 3: P2SH(P2WSH)
        # Try to spend the P2SH output created in the last test.
        # Send it to a P2PKH output, which we'll use in the next test.
        script_pubkey = keyhash_to_p2pkh_script(pubkeyhash)
        tx4 = CTransaction()
        tx4.vin.append(CTxIn(COutPoint(tx3.sha256, 0), script_sig))
        tx4.vout.append(CTxOut(tx3.vout[0].nValue - 1000, script_pubkey))
        tx4.wit.vtxinwit.append(CTxInWitness())
        sign_p2pk_witness_input(witness_program, tx4, 0, SIGHASH_ALL, tx3.vout[0].nValue, key)

        # Should fail policy test.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx4, True, False, 'non-mandatory-script-verify-flag (Using non-compressed keys in segwit)')
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx4])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Test 4: Uncompressed pubkeys should still be valid in non-segwit
        # transactions.
        tx5 = CTransaction()
        tx5.vin.append(CTxIn(COutPoint(tx4.sha256, 0), b""))
        tx5.vout.append(CTxOut(tx4.vout[0].nValue - 1000, CScript([OP_TRUE])))
        (sig_hash, err) = LegacySignatureHash(script_pubkey, tx5, 0, SIGHASH_ALL)
        signature = key.sign_ecdsa(sig_hash) + b'\x01'  # 0x1 is SIGHASH_ALL
        tx5.vin[0].scriptSig = CScript([signature, pubkey])
        tx5.rehash()
        # Should pass policy and consensus.
        test_transaction_acceptance(self.nodes[0], self.test_node, tx5, True, True)
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx5])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
        self.utxo.append(UTXO(tx5.sha256, 0, tx5.vout[0].nValue))

    @subtest  # type: ignore
    def test_signature_version_1(self):

        key = ECKey()
        key.generate()
        pubkey = key.get_pubkey().get_bytes()

        witness_program = CScript([pubkey, CScriptOp(OP_CHECKSIG)])
        script_pubkey = script_to_p2wsh_script(witness_program)

        # First create a witness output for use in the tests.
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()

        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=True, accepted=True)
        # Mine this transaction in preparation for following tests.
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
        self.sync_blocks()
        self.utxo.pop(0)

        # Test each hashtype
        prev_utxo = UTXO(tx.sha256, 0, tx.vout[0].nValue)
        for sigflag in [0, SIGHASH_ANYONECANPAY]:
            for hashtype in [SIGHASH_ALL, SIGHASH_NONE, SIGHASH_SINGLE]:
                hashtype |= sigflag
                block = self.build_next_block()
                tx = CTransaction()
                tx.vin.append(CTxIn(COutPoint(prev_utxo.sha256, prev_utxo.n), b""))
                tx.vout.append(CTxOut(prev_utxo.nValue - 1000, script_pubkey))
                tx.wit.vtxinwit.append(CTxInWitness())
                # Too-large input value
                sign_p2pk_witness_input(witness_program, tx, 0, hashtype, prev_utxo.nValue + 1, key)
                self.update_witness_block_with_transactions(block, [tx])
                test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

                # Too-small input value
                sign_p2pk_witness_input(witness_program, tx, 0, hashtype, prev_utxo.nValue - 1, key)
                block.vtx.pop()  # remove last tx
                self.update_witness_block_with_transactions(block, [tx])
                test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

                # Now try correct value
                sign_p2pk_witness_input(witness_program, tx, 0, hashtype, prev_utxo.nValue, key)
                block.vtx.pop()
                self.update_witness_block_with_transactions(block, [tx])
                test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

                prev_utxo = UTXO(tx.sha256, 0, tx.vout[0].nValue)

        # Test combinations of signature hashes.
        # Split the utxo into a lot of outputs.
        # Randomly choose up to 10 to spend, sign with different hashtypes, and
        # output to a random number of outputs.  Repeat NUM_SIGHASH_TESTS times.
        # Ensure that we've tested a situation where we use SIGHASH_SINGLE with
        # an input index > number of outputs.
        NUM_SIGHASH_TESTS = 500
        temp_utxos = []
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(prev_utxo.sha256, prev_utxo.n), b""))
        split_value = prev_utxo.nValue // NUM_SIGHASH_TESTS
        for _ in range(NUM_SIGHASH_TESTS):
            tx.vout.append(CTxOut(split_value, script_pubkey))
        tx.wit.vtxinwit.append(CTxInWitness())
        sign_p2pk_witness_input(witness_program, tx, 0, SIGHASH_ALL, prev_utxo.nValue, key)
        for i in range(NUM_SIGHASH_TESTS):
            temp_utxos.append(UTXO(tx.sha256, i, split_value))

        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        block = self.build_next_block()
        used_sighash_single_out_of_bounds = False
        for i in range(NUM_SIGHASH_TESTS):
            # Ping regularly to keep the connection alive
            if (not i % 100):
                self.test_node.sync_with_ping()
            # Choose random number of inputs to use.
            num_inputs = random.randint(1, 10)
            # Create a slight bias for producing more utxos
            num_outputs = random.randint(1, 11)
            random.shuffle(temp_utxos)
            assert len(temp_utxos) > num_inputs
            tx = CTransaction()
            total_value = 0
            for i in range(num_inputs):
                tx.vin.append(CTxIn(COutPoint(temp_utxos[i].sha256, temp_utxos[i].n), b""))
                tx.wit.vtxinwit.append(CTxInWitness())
                total_value += temp_utxos[i].nValue
            split_value = total_value // num_outputs
            for _ in range(num_outputs):
                tx.vout.append(CTxOut(split_value, script_pubkey))
            for i in range(num_inputs):
                # Now try to sign each input, using a random hashtype.
                anyonecanpay = 0
                if random.randint(0, 1):
                    anyonecanpay = SIGHASH_ANYONECANPAY
                hashtype = random.randint(1, 3) | anyonecanpay
                sign_p2pk_witness_input(witness_program, tx, i, hashtype, temp_utxos[i].nValue, key)
                if (hashtype == SIGHASH_SINGLE and i >= num_outputs):
                    used_sighash_single_out_of_bounds = True
            tx.rehash()
            for i in range(num_outputs):
                temp_utxos.append(UTXO(tx.sha256, i, split_value))
            temp_utxos = temp_utxos[num_inputs:]

            block.vtx.append(tx)

            # Test the block periodically, if we're close to maxblocksize
            if (get_virtual_size(block) > MAX_BLOCK_BASE_SIZE - 1000):
                self.update_witness_block_with_transactions(block, [])
                test_witness_block(self.nodes[0], self.test_node, block, accepted=True)
                block = self.build_next_block()

        if (not used_sighash_single_out_of_bounds):
            self.log.info("WARNING: this test run didn't attempt SIGHASH_SINGLE with out-of-bounds index value")
        # Test the transactions we've added to the block
        if (len(block.vtx) > 1):
            self.update_witness_block_with_transactions(block, [])
            test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        # Now test witness version 0 P2PKH transactions
        pubkeyhash = hash160(pubkey)
        script_pkh = key_to_p2wpkh_script(pubkey)
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(temp_utxos[0].sha256, temp_utxos[0].n), b""))
        tx.vout.append(CTxOut(temp_utxos[0].nValue, script_pkh))
        tx.wit.vtxinwit.append(CTxInWitness())
        sign_p2pk_witness_input(witness_program, tx, 0, SIGHASH_ALL, temp_utxos[0].nValue, key)
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue, CScript([OP_TRUE])))

        script = keyhash_to_p2pkh_script(pubkeyhash)
        sig_hash = SegwitV0SignatureHash(script, tx2, 0, SIGHASH_ALL, tx.vout[0].nValue, True)
        signature = key.sign_ecdsa(sig_hash) + b'\x01'  # 0x1 is SIGHASH_ALL
        print("----------")
        print(str(tx2))
        print("pubkeyhash:"+pubkeyhash.hex())
        print("sig_hash:"+sig_hash.hex())
        print("signature:"+signature.hex())
        print("pubkey:"+pubkey.hex())

        # Now test witness version 0 P2PKH transactions 2
        pubkeyhash = bytes.fromhex("a7fe2841972797cf3307ee81b934263785606eb1")
        tx2 = CTransaction()
        from_hex(tx2, "0200000000010144eb7fc15aaf597650c0f175246d3be79c8744441e066ab0004595a248693f1f0100000000ffffffff02d06d00000000000017a914e358927656d0e12f263d2cd5809cad358660dbeb87ce97000000000000160014ebedc402510fbe1e1236b7b32a3b3821d93ce98302483045022100ae981fefd7910b847e1db799197bb31f4729b2f0362c0f4db8fecda8b4b5fed502207915eb86fb4c79bfa893d7b2c0126bc7f66ca3dc6ffa7ea0af6aff96cff464e40121029c3589bf8a3b742715ad9b009a8248aaba47497b88339f8cf45f86c7cf563e5a00000000")
        script = keyhash_to_p2pkh_script(pubkeyhash)
        sig_hash = SegwitV0SignatureHash(script, tx2, 0, SIGHASH_ALL, tx.vout[0].nValue, True)
        signature = key.sign_ecdsa(sig_hash) + b'\x01'  # 0x1 is SIGHASH_ALL
        print("----------")
        print(str(tx2))
        print("pubkeyhash:"+pubkeyhash.hex())
        print("sig_hash:"+sig_hash.hex())
        # print("signature:"+signature.hex())
        # print("pubkey:"+pubkey.hex())

        # Check that we can't have a scriptSig
        tx2.vin[0].scriptSig = CScript([signature, pubkey])
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx, tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=False)

        # Move the signature to the witness.
        block.vtx.pop()
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [signature, pubkey]
        tx2.vin[0].scriptSig = b""
        tx2.rehash()

        self.update_witness_block_with_transactions(block, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        temp_utxos.pop(0)

        # Update self.utxos for later tests by creating two outputs
        # that consolidate all the coins in temp_utxos.
        output_value = sum(i.nValue for i in temp_utxos) // 2

        tx = CTransaction()
        index = 0
        # Just spend to our usual anyone-can-spend output
        tx.vout = [CTxOut(output_value, CScript([OP_TRUE]))] * 2
        for i in temp_utxos:
            # Use SIGHASH_ALL|SIGHASH_ANYONECANPAY so we can build up
            # the signatures as we go.
            tx.vin.append(CTxIn(COutPoint(i.sha256, i.n), b""))
            tx.wit.vtxinwit.append(CTxInWitness())
            sign_p2pk_witness_input(witness_program, tx, index, SIGHASH_ALL | SIGHASH_ANYONECANPAY, i.nValue, key)
            index += 1
        block = self.build_next_block()
        self.update_witness_block_with_transactions(block, [tx])
        test_witness_block(self.nodes[0], self.test_node, block, accepted=True)

        for i in range(len(tx.vout)):
            self.utxo.append(UTXO(tx.sha256, i, tx.vout[i].nValue))

    @subtest  # type: ignore
    def test_non_standard_witness_blinding(self):
        """Test behavior of unnecessary witnesses in transactions does not blind the node for the transaction"""

        # Create a p2sh output -- this is so we can pass the standardness
        # rules (an anyone-can-spend OP_TRUE would be rejected, if not wrapped
        # in P2SH).
        p2sh_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2sh_script(p2sh_program)

        # Now check that unnecessary witnesses can't be used to blind a node
        # to a transaction, eg by violating standardness checks.
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, False, True)
        self.nodes[0].generate(1)
        self.sync_blocks()

        # We'll add an unnecessary witness to this transaction that would cause
        # it to be non-standard, to test that violating policy with a witness
        # doesn't blind a node to a transaction.  Transactions
        # rejected for having a witness shouldn't be added
        # to the rejection cache.
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), CScript([p2sh_program])))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, script_pubkey))
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [b'a' * 400]
        tx2.rehash()
        # This will be rejected due to a policy check:
        # No witness is allowed, since it is not a witness program but a p2sh program
        test_transaction_acceptance(self.nodes[1], self.std_node, tx2, True, False, 'bad-witness-nonstandard')

        # If we send without witness, it should be accepted.
        test_transaction_acceptance(self.nodes[1], self.std_node, tx2, False, True)

        # Now create a new anyone-can-spend utxo for the next test.
        tx3 = CTransaction()
        tx3.vin.append(CTxIn(COutPoint(tx2.sha256, 0), CScript([p2sh_program])))
        tx3.vout.append(CTxOut(tx2.vout[0].nValue - 1000, CScript([OP_TRUE, OP_DROP] * 15 + [OP_TRUE])))
        tx3.rehash()
        test_transaction_acceptance(self.nodes[0], self.test_node, tx2, False, True)
        test_transaction_acceptance(self.nodes[0], self.test_node, tx3, False, True)

        self.nodes[0].generate(1)
        self.sync_blocks()

        # Update our utxo list; we spent the first entry.
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx3.sha256, 0, tx3.vout[0].nValue))

    @subtest  # type: ignore
    def test_non_standard_witness(self):
        """Test detection of non-standard P2WSH witness"""
        pad = chr(1).encode('latin-1')

        # Create scripts for tests
        scripts = []
        scripts.append(CScript([OP_DROP] * 100))
        scripts.append(CScript([OP_DROP] * 99))
        scripts.append(CScript([pad * 59] * 59 + [OP_DROP] * 60))
        scripts.append(CScript([pad * 59] * 59 + [OP_DROP] * 61))

        p2wsh_scripts = []

        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))

        # For each script, generate a pair of P2WSH and P2SH-P2WSH output.
        outputvalue = (self.utxo[0].nValue - 1000) // (len(scripts) * 2)
        for i in scripts:
            p2wsh = script_to_p2wsh_script(i)
            p2wsh_scripts.append(p2wsh)
            tx.vout.append(CTxOut(outputvalue, p2wsh))
            tx.vout.append(CTxOut(outputvalue, script_to_p2sh_script(p2wsh)))
        tx.rehash()
        txid = tx.sha256
        test_transaction_acceptance(self.nodes[0], self.test_node, tx, with_witness=False, accepted=True)

        self.nodes[0].generate(1)
        self.sync_blocks()

        # Creating transactions for tests
        p2wsh_txs = []
        p2sh_txs = []
        for i in range(len(scripts)):
            p2wsh_tx = CTransaction()
            p2wsh_tx.vin.append(CTxIn(COutPoint(txid, i * 2)))
            p2wsh_tx.vout.append(CTxOut(outputvalue - 5000, CScript([OP_0, hash160(b"")])))
            p2wsh_tx.wit.vtxinwit.append(CTxInWitness())
            p2wsh_tx.rehash()
            p2wsh_txs.append(p2wsh_tx)
            p2sh_tx = CTransaction()
            p2sh_tx.vin.append(CTxIn(COutPoint(txid, i * 2 + 1), CScript([p2wsh_scripts[i]])))
            p2sh_tx.vout.append(CTxOut(outputvalue - 5000, CScript([OP_0, hash160(b"")])))
            p2sh_tx.wit.vtxinwit.append(CTxInWitness())
            p2sh_tx.rehash()
            p2sh_txs.append(p2sh_tx)

        # Testing native P2WSH
        # Witness stack size, excluding witnessScript, over 100 is non-standard
        p2wsh_txs[0].wit.vtxinwit[0].scriptWitness.stack = [pad] * 101 + [scripts[0]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2wsh_txs[0], True, False, 'bad-witness-nonstandard')
        # Non-standard nodes should accept
        test_transaction_acceptance(self.nodes[0], self.test_node, p2wsh_txs[0], True, True)

        # Stack element size over 80 bytes is non-standard
        p2wsh_txs[1].wit.vtxinwit[0].scriptWitness.stack = [pad * 81] * 100 + [scripts[1]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2wsh_txs[1], True, False, 'bad-witness-nonstandard')
        # Non-standard nodes should accept
        test_transaction_acceptance(self.nodes[0], self.test_node, p2wsh_txs[1], True, True)
        # Standard nodes should accept if element size is not over 80 bytes
        p2wsh_txs[1].wit.vtxinwit[0].scriptWitness.stack = [pad * 80] * 100 + [scripts[1]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2wsh_txs[1], True, True)

        # witnessScript size at 3600 bytes is standard
        p2wsh_txs[2].wit.vtxinwit[0].scriptWitness.stack = [pad, pad, scripts[2]]
        test_transaction_acceptance(self.nodes[0], self.test_node, p2wsh_txs[2], True, True)
        test_transaction_acceptance(self.nodes[1], self.std_node, p2wsh_txs[2], True, True)

        # witnessScript size at 3601 bytes is non-standard
        p2wsh_txs[3].wit.vtxinwit[0].scriptWitness.stack = [pad, pad, pad, scripts[3]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2wsh_txs[3], True, False, 'bad-witness-nonstandard')
        # Non-standard nodes should accept
        test_transaction_acceptance(self.nodes[0], self.test_node, p2wsh_txs[3], True, True)

        # Repeating the same tests with P2SH-P2WSH
        p2sh_txs[0].wit.vtxinwit[0].scriptWitness.stack = [pad] * 101 + [scripts[0]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2sh_txs[0], True, False, 'bad-witness-nonstandard')
        test_transaction_acceptance(self.nodes[0], self.test_node, p2sh_txs[0], True, True)
        p2sh_txs[1].wit.vtxinwit[0].scriptWitness.stack = [pad * 81] * 100 + [scripts[1]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2sh_txs[1], True, False, 'bad-witness-nonstandard')
        test_transaction_acceptance(self.nodes[0], self.test_node, p2sh_txs[1], True, True)
        p2sh_txs[1].wit.vtxinwit[0].scriptWitness.stack = [pad * 80] * 100 + [scripts[1]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2sh_txs[1], True, True)
        p2sh_txs[2].wit.vtxinwit[0].scriptWitness.stack = [pad, pad, scripts[2]]
        test_transaction_acceptance(self.nodes[0], self.test_node, p2sh_txs[2], True, True)
        test_transaction_acceptance(self.nodes[1], self.std_node, p2sh_txs[2], True, True)
        p2sh_txs[3].wit.vtxinwit[0].scriptWitness.stack = [pad, pad, pad, scripts[3]]
        test_transaction_acceptance(self.nodes[1], self.std_node, p2sh_txs[3], True, False, 'bad-witness-nonstandard')
        test_transaction_acceptance(self.nodes[0], self.test_node, p2sh_txs[3], True, True)

        self.nodes[0].generate(1)  # Mine and clean up the mempool of non-standard node
        # Valid but non-standard transactions in a block should be accepted by standard node
        self.sync_blocks()
        assert_equal(len(self.nodes[0].getrawmempool()), 0)
        assert_equal(len(self.nodes[1].getrawmempool()), 0)

        self.utxo.pop(0)

    @subtest  # type: ignore
    def test_upgrade_after_activation(self):
        """Test the behavior of starting up a segwit-aware node after the softfork has activated."""

        # All nodes are caught up and node 2 is a pre-segwit node that will soon upgrade.
        for n in range(2):
            assert_equal(self.nodes[n].getblockcount(), self.nodes[2].getblockcount())
            assert softfork_active(self.nodes[n], "segwit")
        assert SEGWIT_HEIGHT < self.nodes[2].getblockcount()
        assert 'segwit' not in self.nodes[2].getblockchaininfo()['softforks']

        # Restarting node 2 should result in a shutdown because the blockchain consists of
        # insufficiently validated blocks per segwit consensus rules.
        self.stop_node(2)
        self.nodes[2].assert_start_raises_init_error(
            extra_args=[f"-segwitheight={SEGWIT_HEIGHT}"],
            expected_msg=f": Witness data for blocks after height {SEGWIT_HEIGHT} requires validation. Please restart with -reindex..\nPlease restart with -reindex or -reindex-chainstate to recover.",
        )

        # As directed, the user restarts the node with -reindex
        self.start_node(2, extra_args=["-reindex", f"-segwitheight={SEGWIT_HEIGHT}"])

        # With the segwit consensus rules, the node is able to validate only up to SEGWIT_HEIGHT - 1
        assert_equal(self.nodes[2].getblockcount(), SEGWIT_HEIGHT - 1)
        self.connect_nodes(0, 2)

        # We reconnect more than 100 blocks, give it plenty of time
        # sync_blocks() also verifies the best block hash is the same for all nodes
        self.sync_blocks(timeout=240)

        # The upgraded node should now have segwit activated
        assert softfork_active(self.nodes[2], "segwit")

    @subtest  # type: ignore
    def test_witness_sigops(self):
        """Test sigop counting is correct inside witnesses."""

        # Keep this under MAX_OPS_PER_SCRIPT (201)
        witness_program = CScript([OP_TRUE, OP_IF, OP_TRUE, OP_ELSE] + [OP_CHECKMULTISIG] * 5 + [OP_CHECKSIG] * 193 + [OP_ENDIF])
        script_pubkey = script_to_p2wsh_script(witness_program)

        sigops_per_script = 20 * 5 + 193 * 1
        # We'll produce 2 extra outputs, one with a program that would take us
        # over max sig ops, and one with a program that would exactly reach max
        # sig ops
        outputs = (MAX_SIGOP_COST // sigops_per_script) + 2
        extra_sigops_available = MAX_SIGOP_COST % sigops_per_script

        # We chose the number of checkmultisigs/checksigs to make this work:
        assert extra_sigops_available < 100  # steer clear of MAX_OPS_PER_SCRIPT

        # This script, when spent with the first
        # N(=MAX_SIGOP_COST//sigops_per_script) outputs of our transaction,
        # would push us just over the block sigop limit.
        witness_program_toomany = CScript([OP_TRUE, OP_IF, OP_TRUE, OP_ELSE] + [OP_CHECKSIG] * (extra_sigops_available + 1) + [OP_ENDIF])
        script_pubkey_toomany = script_to_p2wsh_script(witness_program_toomany)

        # If we spend this script instead, we would exactly reach our sigop
        # limit (for witness sigops).
        witness_program_justright = CScript([OP_TRUE, OP_IF, OP_TRUE, OP_ELSE] + [OP_CHECKSIG] * (extra_sigops_available) + [OP_ENDIF])
        script_pubkey_justright = script_to_p2wsh_script(witness_program_justright)

        # First split our available utxo into a bunch of outputs
        split_value = self.utxo[0].nValue // outputs
        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        for _ in range(outputs):
            tx.vout.append(CTxOut(split_value, script_pubkey))
        tx.vout[-2].scriptPubKey = script_pubkey_toomany
        tx.vout[-1].scriptPubKey = script_pubkey_justright
        tx.rehash()

        block_1 = self.build_next_block()
        self.update_witness_block_with_transactions(block_1, [tx])
        test_witness_block(self.nodes[0], self.test_node, block_1, accepted=True)

        tx2 = CTransaction()
        # If we try to spend the first n-1 outputs from tx, that should be
        # too many sigops.
        total_value = 0
        for i in range(outputs - 1):
            tx2.vin.append(CTxIn(COutPoint(tx.sha256, i), b""))
            tx2.wit.vtxinwit.append(CTxInWitness())
            tx2.wit.vtxinwit[-1].scriptWitness.stack = [witness_program]
            total_value += tx.vout[i].nValue
        tx2.wit.vtxinwit[-1].scriptWitness.stack = [witness_program_toomany]
        tx2.vout.append(CTxOut(total_value, CScript([OP_TRUE])))
        tx2.rehash()

        block_2 = self.build_next_block()
        self.update_witness_block_with_transactions(block_2, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block_2, accepted=False)

        # Try dropping the last input in tx2, and add an output that has
        # too many sigops (contributing to legacy sigop count).
        checksig_count = (extra_sigops_available // 4) + 1
        script_pubkey_checksigs = CScript([OP_CHECKSIG] * checksig_count)
        tx2.vout.append(CTxOut(0, script_pubkey_checksigs))
        tx2.vin.pop()
        tx2.wit.vtxinwit.pop()
        tx2.vout[0].nValue -= tx.vout[-2].nValue
        tx2.rehash()
        block_3 = self.build_next_block()
        self.update_witness_block_with_transactions(block_3, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block_3, accepted=False)

        # If we drop the last checksig in this output, the tx should succeed.
        block_4 = self.build_next_block()
        tx2.vout[-1].scriptPubKey = CScript([OP_CHECKSIG] * (checksig_count - 1))
        tx2.rehash()
        self.update_witness_block_with_transactions(block_4, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block_4, accepted=True)

        # Reset the tip back down for the next test
        self.sync_blocks()
        for x in self.nodes:
            x.invalidateblock(block_4.hash)

        # Try replacing the last input of tx2 to be spending the last
        # output of tx
        block_5 = self.build_next_block()
        tx2.vout.pop()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, outputs - 1), b""))
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[-1].scriptWitness.stack = [witness_program_justright]
        tx2.rehash()
        self.update_witness_block_with_transactions(block_5, [tx2])
        test_witness_block(self.nodes[0], self.test_node, block_5, accepted=True)

        # TODO: test p2sh sigop counting

        # Cleanup and prep for next test
        self.utxo.pop(0)
        self.utxo.append(UTXO(tx2.sha256, 0, tx2.vout[0].nValue))

    @subtest  # type: ignore
    def test_superfluous_witness(self):
        # Serialization of tx that puts witness flag to 3 always
        def serialize_with_bogus_witness(tx):
            flags = 3
            r = b""
            r += struct.pack("<i", tx.nVersion)
            if flags:
                dummy = []
                r += ser_vector(dummy)
                r += struct.pack("<B", flags)
            r += ser_vector(tx.vin)
            r += ser_vector(tx.vout)
            if flags & 1:
                if (len(tx.wit.vtxinwit) != len(tx.vin)):
                    # vtxinwit must have the same length as vin
                    tx.wit.vtxinwit = tx.wit.vtxinwit[:len(tx.vin)]
                    for _ in range(len(tx.wit.vtxinwit), len(tx.vin)):
                        tx.wit.vtxinwit.append(CTxInWitness())
                r += tx.wit.serialize()
            r += struct.pack("<I", tx.nLockTime)
            return r

        class msg_bogus_tx(msg_tx):
            def serialize(self):
                return serialize_with_bogus_witness(self.tx)

        self.nodes[0].sendtoaddress(self.nodes[0].getnewaddress(address_type='bech32'), 5)
        self.nodes[0].generate(1)
        unspent = next(u for u in self.nodes[0].listunspent() if u['spendable'] and u['address'].startswith('bcrt'))

        raw = self.nodes[0].createrawtransaction([{"txid": unspent['txid'], "vout": unspent['vout']}], {self.nodes[0].getnewaddress(): 1})
        tx = tx_from_hex(raw)
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decoderawtransaction, hexstring=serialize_with_bogus_witness(tx).hex(), iswitness=True)
        with self.nodes[0].assert_debug_log(['Superfluous witness record']):
            self.test_node.send_and_ping(msg_bogus_tx(tx))
        raw = self.nodes[0].signrawtransactionwithwallet(raw)
        assert raw['complete']
        raw = raw['hex']
        tx = tx_from_hex(raw)
        assert_raises_rpc_error(-22, "TX decode failed", self.nodes[0].decoderawtransaction, hexstring=serialize_with_bogus_witness(tx).hex(), iswitness=True)
        with self.nodes[0].assert_debug_log(['Unknown transaction optional data']):
            self.test_node.send_and_ping(msg_bogus_tx(tx))

    @subtest  # type: ignore
    def test_wtxid_relay(self):
        # Use brand new nodes to avoid contamination from earlier tests
        self.wtx_node = self.nodes[0].add_p2p_connection(TestP2PConn(wtxidrelay=True), services=NODE_NETWORK | NODE_WITNESS)
        self.tx_node = self.nodes[0].add_p2p_connection(TestP2PConn(wtxidrelay=False), services=NODE_NETWORK | NODE_WITNESS)

        # Check wtxidrelay feature negotiation message through connecting a new peer
        def received_wtxidrelay():
            return (len(self.wtx_node.last_wtxidrelay) > 0)
        self.wtx_node.wait_until(received_wtxidrelay)

        # Create a Segwit output from the latest UTXO
        # and announce it to the network
        witness_program = CScript([OP_TRUE])
        script_pubkey = script_to_p2wsh_script(witness_program)

        tx = CTransaction()
        tx.vin.append(CTxIn(COutPoint(self.utxo[0].sha256, self.utxo[0].n), b""))
        tx.vout.append(CTxOut(self.utxo[0].nValue - 1000, script_pubkey))
        tx.rehash()

        # Create a Segwit transaction
        tx2 = CTransaction()
        tx2.vin.append(CTxIn(COutPoint(tx.sha256, 0), b""))
        tx2.vout.append(CTxOut(tx.vout[0].nValue - 1000, script_pubkey))
        tx2.wit.vtxinwit.append(CTxInWitness())
        tx2.wit.vtxinwit[0].scriptWitness.stack = [witness_program]
        tx2.rehash()

        # Announce Segwit transaction with wtxid
        # and wait for getdata
        self.wtx_node.announce_tx_and_wait_for_getdata(tx2, use_wtxid=True)
        with p2p_lock:
            lgd = self.wtx_node.lastgetdata[:]
        assert_equal(lgd, [CInv(MSG_WTX, tx2.calc_sha256(True))])

        # Announce Segwit transaction from non wtxidrelay peer
        # and wait for getdata
        self.tx_node.announce_tx_and_wait_for_getdata(tx2, use_wtxid=False)
        with p2p_lock:
            lgd = self.tx_node.lastgetdata[:]
        assert_equal(lgd, [CInv(MSG_TX|MSG_WITNESS_FLAG, tx2.sha256)])

        # Send tx2 through; it's an orphan so won't be accepted
        with p2p_lock:
            self.wtx_node.last_message.pop("getdata", None)
        test_transaction_acceptance(self.nodes[0], self.wtx_node, tx2, with_witness=True, accepted=False)

        # Expect a request for parent (tx) by txid despite use of WTX peer
        self.wtx_node.wait_for_getdata([tx.sha256], 60)
        with p2p_lock:
            lgd = self.wtx_node.lastgetdata[:]
        assert_equal(lgd, [CInv(MSG_WITNESS_TX, tx.sha256)])

        # Send tx through
        test_transaction_acceptance(self.nodes[0], self.wtx_node, tx, with_witness=False, accepted=True)

        # Check tx2 is there now
        assert_equal(tx2.hash in self.nodes[0].getrawmempool(), True)

def test_sighash():
    pubkeyhash = bytes.fromhex("a7fe2841972797cf3307ee81b934263785606eb1")
    tx2 = CTransaction()
    from_hex(tx2, "0200000000010144eb7fc15aaf597650c0f175246d3be79c8744441e066ab0004595a248693f1f0100000000ffffffff02d06d00000000000017a914e358927656d0e12f263d2cd5809cad358660dbeb87ce97000000000000160014ebedc402510fbe1e1236b7b32a3b3821d93ce98302483045022100ae981fefd7910b847e1db799197bb31f4729b2f0362c0f4db8fecda8b4b5fed502207915eb86fb4c79bfa893d7b2c0126bc7f66ca3dc6ffa7ea0af6aff96cff464e40121029c3589bf8a3b742715ad9b009a8248aaba47497b88339f8cf45f86c7cf563e5a00000000")
    script = keyhash_to_p2pkh_script(pubkeyhash)
    sig_hash = SegwitV0SignatureHash(script, tx2, 0, SIGHASH_ALL, 70212, True)
    print(sig_hash.hex())

    tx2 = CTransaction()
    from_hex(tx2, "0100000001c997a5e56e104102fa209c6a852dd90660a20b2d9c352423edce25857fcd3704000000004847304402204e45e16932b8af514961a1d3a1a25fdf3f4f7732e9d624c6c61548ab5fb8cd410220181522ec8eca07de4860a4acdd12909d831cc56cbbac4622082221a8768d1d0901ffffffff0200ca9a3b00000000434104ae1a62fe09c5f51b13905f07f06b99a2f7159b2225f374cd378d71302fa28414e7aab37397f554a7df5f142c21c1b7303b8a0626f1baded5c72a704f7e6cd84cac00286bee0000000043410411db93e1dcdb8a016b49840f8c53bc1eb68a382e97b1482ecad7b148a6909a5cb2e0eaddfb84ccf9744464f82e160bfa9b8b64f9d4c03f999b8643f656b412a3ac00000000")
    script = CScript([hex_str_to_bytes("0411db93e1dcdb8a016b49840f8c53bc1eb68a382e97b1482ecad7b148a6909a5cb2e0eaddfb84ccf9744464f82e160bfa9b8b64f9d4c03f999b8643f656b412a3"),OP_CHECKSIG])
    sig_hash,t = LegacySignatureHash(script, tx2, 0, SIGHASH_ALL)
    print(sig_hash.hex())

    tx2 = CTransaction()
    from_hex(tx2, "02000000000105295d97f2e490603daa93d081c96098ef247ff5d3aaa44fcd7f9a19e87cb9d1cb070000006a473044022047638130bb532797fd1c1390c1b834ad36e47a3b6023a07ff9f0e10c152276e002204041da96a04bf4c891cbc0a407e0f66368201944067a0b6b9cbece863ffe7fe9012103dd9e32e84f3a6c3990acc44e94a1cd697d0c3aa6a1d885c492e9f84d780dc11bfeffffff7c32bd34db25815a80d379f8f784321c8b8afaa0f3d6dca6660291b93b35f81600000000171600141cc16b517019320db3e60bafd22cbd00b0064e16feffffff8c9008a9a116b18e6fbe69fc47d4b87b3bce8d9c8b5974d76fb0bdbde1ec0a5402000000171600146c67b866334fbdb7b8bad90541b0da04ca4f122cfeffffff9281a1d18546898684ccd2224f2a98cc6506498f0e10c29b1ee03c18e4e995650c000000171600146108b4fb21f1dd7eae5797037d75015cc6fb74ccfeffffffddc131d68ad726b93a955ae66b444384111f85737dab7748d7eede25c0e79fbb0000000017160014a511d4ef762f51499f6516f631c69f5659303674feffffff0236790d000000000017a914b5d50e3e894cb36992ee8c08859c25d176cb3d8587f6e13c040000000017a914ab9f384896b5a83deefb53e07b30ff52f2ed4f3187000247304402207bf42a800de6e62c27172393fc6fd1443bba0783db5a2a56a7ff11ce9b6665cf022074ff9d4e824a4d7deddaca1df04c5fdc61a68551133b4fe1bd3dbf2fead22daf012103c0af94e9899febc8487948ee60d7a872162f555185b7acef3fec0531973d75c1024830450221009a5e451ba41abd8b54cf2a53d30ddc88e97f772d3f1d7b96101c4c0680f02a9f0220444c5f71caa638d182a7dca169610698eed9d32bb46d78f484ed98414e98984a0121027015eca0d22a972c115b5a87a544f7fd1357749cde548ac7bae2b90254f91761024830450221009a2600537b0d97f44f0f0652fbe720c50519e598253cbf0de45dbc2b43eb584b0220561693c027f416c74f0f5fb29477c76cfbe37eb4b84fb4345aa524086998148201210260338103fc83fab25f7b0bb6d4951392affb44d3085e7f45784d462477ff359e02473044022006afc06b8769dcaa46f5a2f3c6506b67309e810a5cb82639143310c4e3db1b9002202b942f6a3ca0618ed07b3b7967330822d8dc1a636def13abfb493d0c92391ff2012103f31a874df957f8ac6569c5f3a56bf1666ee44fe2e540916704f70c5023c815c8be270900")
    script = CScript([OP_DUP ,OP_HASH160 ,hex_str_to_bytes("24241ef3a9ef1c11f489631d0c9a2710ad1fc304"), OP_EQUALVERIFY, OP_CHECKSIG])
    sig_hash,t = LegacySignatureHash(script, tx2, 0, SIGHASH_ALL)
    print(sig_hash.hex())


    tx2 = CTransaction()
    from_hex(tx2, "02000000000105295d97f2e490603daa93d081c96098ef247ff5d3aaa44fcd7f9a19e87cb9d1cb070000006a473044022047638130bb532797fd1c1390c1b834ad36e47a3b6023a07ff9f0e10c152276e002204041da96a04bf4c891cbc0a407e0f66368201944067a0b6b9cbece863ffe7fe9012103dd9e32e84f3a6c3990acc44e94a1cd697d0c3aa6a1d885c492e9f84d780dc11bfeffffff7c32bd34db25815a80d379f8f784321c8b8afaa0f3d6dca6660291b93b35f81600000000171600141cc16b517019320db3e60bafd22cbd00b0064e16feffffff8c9008a9a116b18e6fbe69fc47d4b87b3bce8d9c8b5974d76fb0bdbde1ec0a5402000000171600146c67b866334fbdb7b8bad90541b0da04ca4f122cfeffffff9281a1d18546898684ccd2224f2a98cc6506498f0e10c29b1ee03c18e4e995650c000000171600146108b4fb21f1dd7eae5797037d75015cc6fb74ccfeffffffddc131d68ad726b93a955ae66b444384111f85737dab7748d7eede25c0e79fbb0000000017160014a511d4ef762f51499f6516f631c69f5659303674feffffff0236790d000000000017a914b5d50e3e894cb36992ee8c08859c25d176cb3d8587f6e13c040000000017a914ab9f384896b5a83deefb53e07b30ff52f2ed4f3187000247304402207bf42a800de6e62c27172393fc6fd1443bba0783db5a2a56a7ff11ce9b6665cf022074ff9d4e824a4d7deddaca1df04c5fdc61a68551133b4fe1bd3dbf2fead22daf012103c0af94e9899febc8487948ee60d7a872162f555185b7acef3fec0531973d75c1024830450221009a5e451ba41abd8b54cf2a53d30ddc88e97f772d3f1d7b96101c4c0680f02a9f0220444c5f71caa638d182a7dca169610698eed9d32bb46d78f484ed98414e98984a0121027015eca0d22a972c115b5a87a544f7fd1357749cde548ac7bae2b90254f91761024830450221009a2600537b0d97f44f0f0652fbe720c50519e598253cbf0de45dbc2b43eb584b0220561693c027f416c74f0f5fb29477c76cfbe37eb4b84fb4345aa524086998148201210260338103fc83fab25f7b0bb6d4951392affb44d3085e7f45784d462477ff359e02473044022006afc06b8769dcaa46f5a2f3c6506b67309e810a5cb82639143310c4e3db1b9002202b942f6a3ca0618ed07b3b7967330822d8dc1a636def13abfb493d0c92391ff2012103f31a874df957f8ac6569c5f3a56bf1666ee44fe2e540916704f70c5023c815c8be270900")
    script = CScript([OP_2, hex_str_to_bytes("03abd014d467f75f5c7c32de0cc099117a12291afa14ffddcefc35b873d3429c7b"), hex_str_to_bytes("037d4514706a6d5f9b5ef8a1e7badef1044f1555fabe28cbbd1205c8bec6b68d5e"), OP_2, OP_CHECKMULTISIG])
    sig_hash = SegwitV0SignatureHash(script, tx2, 0, SIGHASH_ALL, 310334, True)
    print(sig_hash.hex())

    tx2 = CTransaction()
    from_hex(tx2, "02000000013bc2b06876e3c47b621cbdaad54e37b60fc30ff54ff2f58c7209d8474e59432c01000000fdfd0000473044022043575e82ae1d65b35db4f7bce791114aecc365e55c95901805dd2e9ecfbe700d022064953d0202becfdeb965faf273f052db9ad7f0e4111143847bae485ae43a953101483045022100c1625a244dc33c0f9696c657035cd55aa720e3c0c96f495c9470c2dcf254fc98022057241a217a8e3a7946e562f439d3ae21f78ac1177408ab2b4afed0cb25840b8f014c6952210356d5b29f4a5e32a77eacffadfb5e5ce5b4e3f99c55092547b65e1e71ad5edc29210279d20cb72cb1caab9d3779a024ece32e6516784fb5f1153b840036729cfe3b362103db09f929b2a19a6a8982986f939ee9154414049687a0b5ffea68258cd42c218453aeffffffff05c042c000000000001976a914a24189f181329823410da2e399f03aa2a1c800da88ac00943577000000001976a914004d69cc96d5cf8f349af31491e154156b4b0dc588ac085a22010000000017a91469f3773f98ca54896e5eae7330a5a0c9befaf7eb87c55c26000000000017a914717fea94c380b0e362690b3b4b259f4d5033c5eb87da7a21c70c00000017a91427c69beb340268f43e6c0fc1305f44b5a404e0c38700000000")
    script = CScript([OP_2, hex_str_to_bytes('0356d5b29f4a5e32a77eacffadfb5e5ce5b4e3f99c55092547b65e1e71ad5edc29'), hex_str_to_bytes('0279d20cb72cb1caab9d3779a024ece32e6516784fb5f1153b840036729cfe3b36'), hex_str_to_bytes('03db09f929b2a19a6a8982986f939ee9154414049687a0b5ffea68258cd42c2184'), OP_3, OP_CHECKMULTISIG])
    sig_hash,t = LegacySignatureHash(script, tx2, 0, SIGHASH_ALL)
    print(sig_hash.hex())


    tx2 = CTransaction()
    from_hex(tx2, "0100000002f9cbafc519425637ba4227f8d0a0b7160b4e65168193d5af39747891de98b5b5000000006b4830450221008dd619c563e527c47d9bd53534a770b102e40faa87f61433580e04e271ef2f960220029886434e18122b53d5decd25f1f4acb2480659fea20aabd856987ba3c3907e0121022b78b756e2258af13779c1a1f37ea6800259716ca4b7f0b87610e0bf3ab52a01ffffffff42e7988254800876b69f24676b3e0205b77be476512ca4d970707dd5c60598ab00000000fd260100483045022015bd0139bcccf990a6af6ec5c1c52ed8222e03a0d51c334df139968525d2fcd20221009f9efe325476eb64c3958e4713e9eefe49bf1d820ed58d2112721b134e2a1a53034930460221008431bdfa72bc67f9d41fe72e94c88fb8f359ffa30b33c72c121c5a877d922e1002210089ef5fc22dd8bfc6bf9ffdb01a9862d27687d424d1fefbab9e9c7176844a187a014c9052483045022015bd0139bcccf990a6af6ec5c1c52ed8222e03a0d51c334df139968525d2fcd20221009f9efe325476eb64c3958e4713e9eefe49bf1d820ed58d2112721b134e2a1a5303210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71210378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c7153aeffffffff01a08601000000000017a914d8dacdadb7462ae15cd906f1878706d0da8660e68700000000")
    script = CScript([OP_2, hex_str_to_bytes('3045022015bd0139bcccf990a6af6ec5c1c52ed8222e03a0d51c334df139968525d2fcd20221009f9efe325476eb64c3958e4713e9eefe49bf1d820ed58d2112721b134e2a1a5303'), hex_str_to_bytes('0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71'), hex_str_to_bytes('0378d430274f8c5ec1321338151e9f27f4c676a008bdf8638d07c0b6be9ab35c71'), OP_3, OP_CHECKMULTISIG])
    sig_hash,t = LegacySignatureHash(script, tx2, 1, 3)
    print(sig_hash.hex())

if __name__ == '__main__':
    test_sighash()
