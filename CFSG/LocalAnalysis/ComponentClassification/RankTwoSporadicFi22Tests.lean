module

public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi22

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer

@[expose] def fi22InPT (t : Array ℕ) : Bool :=
  siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 t

@[expose] def fi22InRT (t : Array ℕ) : Bool :=
  fi22InPT t || fi22InPT (compA 3510 fi22GraphOuterArr t)

@[expose] def fi22PS : List ℕ := [0, 1, 2]

theorem fi22PS_lt : ∀ p ∈ fi22PS, p < 3510 := by decide

end CFSG.ComponentClassification.RankTwoSporadic.Fi22
