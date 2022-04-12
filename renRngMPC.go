package main

import (
	"fmt"
	"github.com/renproject/mpc/mulopen/mulzkp"
	"github.com/renproject/mpc/rkpg/rkpgutil"
	. "github.com/renproject/mpc/brng"
	. "github.com/renproject/mpc/mpcutil"
	"github.com/renproject/mpc/params"
	"github.com/renproject/secp256k1"
	"github.com/renproject/shamir"
	"github.com/renproject/shamir/shamirutil"
	"math/rand"
	"time"
)

/*
PlayerMessage struct stores the sender and receiver
of a massage which is a verifiable share of a secret
from  : sender
to    : receiver
vshare: verifiable share sent to the receiver by sender
*/
type PlayerMessage struct {
	from, to secp256k1.Fn
	msgtype  int
	vshare   shamir.VerifiableShare
}

/*
Represents message types
*/
const (
	state0  = iota  // machine state
	add1
	add2
	state1 			// machine state
	addop1
	addop2
	state2 			// machine state
	mul
	state3			//machine state
	open
	mulopen
	addopen
)

/*
PlayerMachine struct represents one node in network
id            : player id from 1 to n (human readable)
row           : b batches of array of verifiable shares. For this program b = 1
sharesReceived: shares of different secrets(players) received by this player
batchSize     : it is nothing but how many secrets is the player planning to share
		        For this program b = batchSize = 1
ownIndex      : Random ID for a player
h             : blinding factor for commitment
*/ 
type PlayerMachine struct {
	id               		 ID
	state                    int 
	row1              		 []Sharing
	row2              		 []Sharing
	addShares1        		 []PlayerMessage
	addShares2        		 []PlayerMessage
	mulShares        		 []PlayerMessage
	addReceivedSharesOp1     PlayerMessage
	addReceivedSharesOp2     PlayerMessage
	zeroShareOp				 shamir.VerifiableShare
	mulReceivedSharesOp      shamir.VerifiableShare
	mulOpenVal				 secp256k1.Fn
	proof  					 mulzkp.Proof
	a		 				 secp256k1.Point // parameter "a" of proof verification
	b		 				 secp256k1.Point // parameter "b" of proof verification
	c        				 secp256k1.Point // parameter "c" of proof verification
	batchSize        		 uint32
	ownIndex         		 secp256k1.Fn
	h                		 secp256k1.Point
}

// returns a player machine structure
func getPlayerMachine(id ID, state int, row1 []Sharing, row2 []Sharing, batchSize uint32, ownIndex secp256k1.Fn, h secp256k1.Point) PlayerMachine {
	return PlayerMachine{id: id, state:state, row1: row1, row2: row2, batchSize: batchSize, ownIndex: ownIndex, h: h}
}


// this works correctly when batchsize = 1
// Adds messages sent by any player to a hypothetical message pool
// create a handle function to distribute messages in a round robin fashion
func updateMessageBuffer(message_buffer *[]PlayerMessage, row []Sharing, index secp256k1.Fn, indices []secp256k1.Fn, msg_type int) {
	for _, shares := range row {
		for j, sharings := range shares.Shares {
			*message_buffer = append(*message_buffer, PlayerMessage{from: index, to: indices[j], msgtype: msg_type, vshare: sharings})
		}
	}
}


func processMsg(machine map[secp256k1.Fn]PlayerMachine, msg PlayerMessage) (bool, []PlayerMessage){
	var num_of_machines int
	var msgs []PlayerMessage
	num_of_machines = len(machine)
	tmp := machine[msg.to]
	switch msg.msgtype {
    case add1:
        if num_of_machines > len(tmp.addShares1){
        	tmp.addShares1 = append(tmp.addShares1, msg)
        }
    case add2:
        if num_of_machines > len(tmp.addShares2){
        	tmp.addShares2 = append(tmp.addShares2, msg)
        }
    case mul:
    	tmp.mulShares = append(tmp.mulShares, msg)
    case addop1:
    	tmp.addReceivedSharesOp1 = msg
    case addop2:
    	tmp.addReceivedSharesOp2 = msg
    }
    machine[msg.to] = tmp
    if (num_of_machines == len(tmp.addShares1))&&(num_of_machines == len(tmp.addShares2))&&(state0 == tmp.state){
        tmp2 := machine[msg.to]
        fmt.Println("#######################")
        tmp2.state = state1
        machine[msg.to] = tmp2
        v1,v2 := addSharesaSharesb(machine, msg.to)
		msgs = append(msgs, PlayerMessage{from: msg.to, to: msg.to, msgtype: addop1, vshare: v1})
		msgs = append(msgs, PlayerMessage{from: msg.to, to: msg.to, msgtype: addop2, vshare: v2})
		tmp2 = machine[msg.to]
		tmp2.state = state2
		machine[msg.to] = tmp2
    }
    return true, msgs
}

// Maps the message pool content into blocks assigned for different players
// The blocks are then assigned to different machines representing the players
func processMessages(machines map[secp256k1.Fn]PlayerMachine, message_buffer *[]PlayerMessage) {
	var globalState int
	for i:=0; i<len(*message_buffer); i++{
		_, msgs := processMsg(machines, (*message_buffer)[i])
		if 0 < len(msgs){
			for _,m := range msgs{
				*message_buffer = append(*message_buffer, m)
				fmt.Println("New messages added...")
			}
		}
		fmt.Println("i = ",i)
		fmt.Println("len(*message_buffer) = ",len(*message_buffer))
		if (i+1==len(*message_buffer))&&(state3 != globalState){
			mulMachineShares(machines)
			for k,_ := range machines{
				tmp := machines[k]
				tmp.state = state3
				machines[k] = tmp
				for j,_ := range machines{
					*message_buffer = append(*message_buffer, PlayerMessage{from: machines[k].ownIndex, to: machines[j].ownIndex, msgtype: mul, vshare: machines[k].mulReceivedSharesOp})
					fmt.Println("New messages added...")
				}
			}
			globalState = state3
		}
	}
	fmt.Println("#####len(message_buffer) : ",len(*message_buffer))
	for _,machine := range machines{
		if state2 != machine.state{
			fmt.Println("Machine error : ",machine.ownIndex)
		}else{
			fmt.Println("Machine success : ",machine.ownIndex)	
		}
	}
}


func addSharesaSharesb(machines map[secp256k1.Fn]PlayerMachine, index secp256k1.Fn) (shamir.VerifiableShare, shamir.VerifiableShare){
	tmp := machines[index]
	shares_arr1 := tmp.addShares1
	shares_arr2 := tmp.addShares2
	sum_of_shares1 := shares_arr1[0].vshare
	sum_of_shares2 := shares_arr2[0].vshare
	for j, _ := range shares_arr1 {
		if 0 != j {
			sum_of_shares1.Add(&sum_of_shares1, &shares_arr1[j].vshare)
			sum_of_shares2.Add(&sum_of_shares2, &shares_arr2[j].vshare)
		}
	}
	return sum_of_shares1,sum_of_shares2
}

func pedersenCommit(value, decommitment *secp256k1.Fn, h *secp256k1.Point) secp256k1.Point {
	var commitment, hPow secp256k1.Point
	commitment.BaseExp(value)
	hPow.Scale(h, decommitment)
	commitment.Add(&commitment, &hPow)
	return commitment
}

func mulMachineShares(machines map[secp256k1.Fn]PlayerMachine){
	fmt.Println("Inside mulMachineShares")
	var product secp256k1.Fn
	for i, _ := range machines {
		tmp := machines[i]
		product = tmp.addReceivedSharesOp1.vshare.Share.Value
		product.Mul(&product, &tmp.addReceivedSharesOp2.vshare.Share.Value)
		tau := secp256k1.RandomFn()
		aShareCommitment := pedersenCommit(&tmp.addReceivedSharesOp1.vshare.Share.Value, &tmp.addReceivedSharesOp1.vshare.Decommitment, &tmp.h)
		bShareCommitment := pedersenCommit(&tmp.addReceivedSharesOp2.vshare.Share.Value, &tmp.addReceivedSharesOp2.vshare.Decommitment, &tmp.h)
		productShareCommitment := pedersenCommit(&product, &tau, &tmp.h)
		proof := mulzkp.CreateProof(&tmp.h, &aShareCommitment, &bShareCommitment, &productShareCommitment,
			tmp.addReceivedSharesOp1.vshare.Share.Value, tmp.addReceivedSharesOp2.vshare.Share.Value,
			tmp.addReceivedSharesOp1.vshare.Decommitment, tmp.addReceivedSharesOp1.vshare.Decommitment, tau,
		)
		//tmp.mulReceivedSharesOp = product
		share := shamir.VerifiableShare{
			Share: shamir.Share{
				Index: tmp.ownIndex,
				Value: product,
			},
			Decommitment: tau,
		}
		share.Add(&share, &tmp.zeroShareOp)
		tmp.mulReceivedSharesOp = share
		tmp.a = aShareCommitment
		tmp.b = bShareCommitment
		tmp.c = productShareCommitment
		tmp.proof = proof
		machines[i] = tmp
	}
}

func openMul(machines map[secp256k1.Fn]PlayerMachine){
	for i,_ := range machines{
		tmp := machines[i]
		if mulzkp.Verify(&tmp.h, &tmp.a, &tmp.b, &tmp.c, &tmp.proof){
			fmt.Println("Proof Verified !!!!")
		}else{
			fmt.Println("Proof Not Verified !!!!")
		}
		shares_arr := make(shamir.Shares, 0)
		for _, x := range tmp.mulShares {
			shares_arr = append(shares_arr, x.vshare.Share)
		}
		open_val := shamir.Open(shares_arr)
		tmp.mulOpenVal = open_val
		machines[i] = tmp
	}
}

// Gets the sum of all the secrets of different players
// Its output must match with that of addMachineSharesAndInterpolate(machines)
func getSumOfSecrets(secret_arr []secp256k1.Fn) secp256k1.Fn {
	sum := secret_arr[0]
	for i, secrets := range secret_arr {
		if 0 != i {
			sum.Add(&sum, &secrets)
		}
	}
	return sum
}

func genRandomParameters() (int, uint32, uint32, int, []secp256k1.Fn, secp256k1.Fn, secp256k1.Point) {
	n := shamirutil.RandRange(5, 20)
	k := shamirutil.RandRange(1, (n/2)-1)
	b := shamirutil.RandRange(1, 5)
	t := shamirutil.RandRange(k, n)
	indices := shamirutil.RandomIndices(n)
	index := indices[rand.Intn(len(indices))]
	h := secp256k1.RandomPoint()
	return n, uint32(k), uint32(b), t, indices, index, h
}

func NewShares(batchSize, k uint32, indices []secp256k1.Fn, index secp256k1.Fn, h secp256k1.Point) ([]Sharing, []secp256k1.Fn) {
	if batchSize < 1 {
		panic(fmt.Sprintf("batch size must be at least 1: got %v", batchSize))
	}
	if k < 1 {
		panic(fmt.Sprintf("k must be at least 1: got %v", k))
	}
	if !params.ValidPedersenParameter(h) {
		panic("insecure choice of pedersen parameter")
	}
	secret_arr := make([]secp256k1.Fn, 0)
	n := len(indices)
	sharings := make([]Sharing, int(batchSize))
	for i := range sharings {
		sharings[i].Shares = make(shamir.VerifiableShares, n)
		sharings[i].Commitment = shamir.NewCommitmentWithCapacity(int(k))
		secret := secp256k1.RandomFn()
		secret_arr = append(secret_arr, secret)
		shamir.VShareSecret(&sharings[i].Shares, &sharings[i].Commitment,
			indices, h, secret, int(k))
	}
	return sharings, secret_arr
}

func main() {
	rand.Seed(int64(time.Now().Nanosecond()))
	_, k, b, _, indices, _, h := genRandomParameters()
	b = 1
	var zeroShares shamir.VerifiableShares
	//var zeroComs shamir.Commitment
	// simulating a network machine
	playerIDs := make([]ID, len(indices))
	machines := make(map[secp256k1.Fn]PlayerMachine, 0)
	secret_arr_1 := make([]secp256k1.Fn, 0)
	secret_arr_2 := make([]secp256k1.Fn, 0)
	var message_buffer = make([]PlayerMessage, 0)
	for i := range playerIDs {
		playerIDs[i] = ID(i + 1)
	}
	fmt.Println("playerIDs = ", playerIDs)
	consID := ID(len(indices) + 1)
	fmt.Println("consID = ", consID)

	for i, id := range playerIDs {
		index := indices[i]
		row_1, secret_arr_ret_1 := NewShares(b, k, indices, index, h)
		secret_arr_1 = append(secret_arr_1, secret_arr_ret_1[0])
		row_2, secret_arr_ret_2 := NewShares(b, k, indices, index, h)
		secret_arr_2 = append(secret_arr_2, secret_arr_ret_2[0])
		machine := getPlayerMachine(id, state0, row_1, row_2, b, index, h)
		updateMessageBuffer(&message_buffer, row_1, index, indices, add1)
		updateMessageBuffer(&message_buffer, row_2, index, indices, add2)
		machines[index] = machine
	}

	// ---- Give a share of zero to each player in a centralised way for simplicity ---- //

	zeroShares, _ = rkpgutil.RXGOutput(indices, int(k), h, secp256k1.NewFnFromU16(0))

	for i,index :=range indices{
		tmp := machines[index]
		tmp.zeroShareOp = zeroShares[i]
		machines[index] = tmp
	}

	// ---- Give a share of zero to each player in a centralised way for simplicity ---- //

	// ---- shuffle message buffer ----//
	rand.Shuffle(len(message_buffer), func(i, j int) { message_buffer[i], message_buffer[j] = message_buffer[j], message_buffer[i] })
	// ---- shuffle message buffer ----//
	
	processMessages(machines, &message_buffer)

	// ---- perform open ---- //
	openMul(machines)
	// ---- perform open ---- //

	// ---- verify ---- //
	var verify_mulopen secp256k1.Fn
	var verify_flag bool
	verify_flag = false
	for i,_ := range machines{
		if !verify_flag{
			verify_mulopen = machines[i].mulOpenVal
			verify_flag = true
		} else{
			if verify_mulopen != machines[i].mulOpenVal{
				verify_flag = false
				break
			}
		}
	}
	if verify_flag{
		fmt.Println("Mulopen correctly verified.")
	} else{
		fmt.Println("Mulopen inconsistent!!!")
	}
	// ---- verify ---- //

}
