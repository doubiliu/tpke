package tpke

import (
	"math/rand"
	"time"

	rng "github.com/leesper/go_rng"
	"github.com/phoreproject/bls"
)

type PublicKey struct {
	g1 *bls.G1Projective
}

func NewPublicKey(scs []SecretCommitment) *PublicKey {
	g1 := scs[0].commitment.coeff[0].Copy()
	for i := 0; i < len(scs); i++ {
		g1 = g1.Add(scs[i].commitment.coeff[0])
	}
	return &PublicKey{
		g1: g1,
	}
}

func (pk *PublicKey) Encrypt(msg *bls.G1Projective) *CipherText {
	s1 := rand.NewSource(time.Now().UnixNano())
	r1 := rand.New(s1)
	uRng := rng.NewUniformGenerator(int64(r1.Int()))
	r := bls.NewFRRepr(uint64(uRng.Int64()))

	g1 := msg.Add(pk.g1.MulFR(r))
	bigR := bls.G1ProjectiveOne.MulFR(r)

	return &CipherText{
		g1:   g1,
		bigR: bigR,
	}
}
