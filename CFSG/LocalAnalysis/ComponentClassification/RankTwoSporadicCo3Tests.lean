module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicDecodeR
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.Sporadic.Schreier.Co3OrderCheckInputs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co3

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier.Co3
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def co3InP (t : Array ℕ) : Bool :=
  siftA 276 (rawLevels 276 co3ChainArrs co3ChainBaseArr) co3ChainBaseArr 0 t

@[expose] def co3Gens : Array (Array ℕ) := #[co3ChainArrs[0]!, co3ChainArrs[1]!]

@[expose] def co3PS : List ℕ := [0, 1, 2, 3, 4, 5, 6]

@[expose] def co3Fuel : ℕ := 2 ^ 20

theorem co3PS_lt : ∀ p ∈ co3PS, p < 276 := by decide

@[expose] def co3Check (sc sp : String) : Bool :=
  let d := decodeCertR (slpRegs 276 co3Gens (decodePairs sp)) sc
  censusOK 276 co3PS co3Fuel co3InP co3InP false false false d.sGens d.roots d.nodes &&
    (allLt d.sGens.size fun k =>
      co3InP d.sGens[k]! || co3InP (compA 276 (idA 276) d.sGens[k]!)) &&
    (CFSG.RankThree.Native.enumBfs 276 d.sGens co3PS co3Fuel).pts.size == 1024

end CFSG.ComponentClassification.RankTwoSporadic.Co3
