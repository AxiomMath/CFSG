module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Gen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Weak

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open GF64

@[expose] def p1Gen : GenData where
  gens := #[#[ofNat' 0, ofNat' 22, ofNat' 0, ofNat' 0, ofNat' 0, ofNat' 52, ofNat' 52, ofNat' 0,
      ofNat' 0], #[ofNat' 24, ofNat' 40, ofNat' 56, ofNat' 56, ofNat' 24, ofNat' 40, ofNat' 40,
      ofNat' 56, ofNat' 24]]
  v0 := #[0, 1, 1]
  words := [[0, 2, 2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 1, 3, 0, 2, 2, 1, 2, 2, 2, 2, 1, 3, 3, 0, 3, 3,
      3, 3, 0, 2, 1, 2, 2, 2], [2, 2, 0, 2, 0, 0, 2, 0, 0, 2, 2, 1, 2, 1, 2, 1, 1, 2, 0, 3, 3, 1,
      1, 3, 0, 2, 1, 2, 1, 2, 0, 2, 2, 0, 3, 1, 3, 1, 3, 3, 0, 3, 0, 3, 0, 2, 1], [2, 0, 0, 2, 2,
      2, 0, 0, 2, 1, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 3, 1, 3, 3, 0, 2, 0, 2, 0, 2, 0, 3, 0, 2, 0, 3,
      1, 2, 2, 0, 2, 1], [0, 2, 0, 3, 0, 2, 0, 3, 1, 2, 2, 0, 2, 1, 1, 2, 2, 0, 2, 0, 3, 1, 2, 0,
      3, 1, 3, 3, 1, 3, 3, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3], [0, 2, 2, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2,
      2, 2, 1, 2, 0, 3, 3, 1, 3], [1, 2, 1, 3, 3, 0, 3, 0, 2, 1, 3, 0, 3, 3, 1, 3, 3, 1, 3, 0, 3,
      0, 3, 1, 2, 0, 3, 3, 0, 3, 1, 3, 1, 3, 1, 1, 3, 3, 1, 3]]
  fuel1 := 33000
  fuel2 := 600

@[expose] def p1Data : CheckData where
  e := #[(#[ofNat' 0, ofNat' 1, ofNat' 0, ofNat' 0, ofNat' 0, ofNat' 1, ofNat' 1, ofNat' 0,
      ofNat' 0], 0), (#[ofNat' 1, ofNat' 0, ofNat' 0, ofNat' 0, ofNat' 9, ofNat' 0, ofNat' 0,
      ofNat' 0, ofNat' 8], 0), (#[ofNat' 1, ofNat' 0, ofNat' 0, ofNat' 0, ofNat' 1, ofNat' 0,
      ofNat' 0, ofNat' 0, ofNat' 1], 1)]
  g := #[(p1Gen.gens.getD 0 #[], 0), (p1Gen.gens.getD 1 #[], 0)]
  fv := #[#[0, 1, 0], #[1, 0, 2], #[0, 0, 1], #[1, 0, 0]]
  cj := #[1, 0, 1, 1, 1, 2, 0, 1]

@[expose] def p1Sc : List GF64 :=
  [GF64.ofNat' 1, GF64.ofNat' 8, GF64.ofNat' 9]

end CFSG.AGLEmbedding.ChevOuter.U38
