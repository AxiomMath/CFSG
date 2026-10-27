module

public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck
public import CFSG.Sporadic.SmallOddCore.McLData

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.McL

open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier

@[expose] def mclInP (t : Array ℕ) : Bool :=
  siftA 275 (rawLevels 275 mclStrongArrs PairMcL.baseArr) PairMcL.baseArr 0 t

@[expose] def mclUArr : Array ℕ :=
  CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl

@[expose] def mclPS : List ℕ := [0, 1, 2, 3, 4, 5]

theorem mclPS_lt : ∀ p ∈ mclPS, p < 275 := by decide

end CFSG.ComponentClassification.RankTwoSporadic.McL
