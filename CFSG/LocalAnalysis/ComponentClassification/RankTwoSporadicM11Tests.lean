module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheck

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M11

open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def m11Gens : Array (Array ℕ) :=
  #[#[0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3], #[3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]]

@[expose] def m11PS : List ℕ := [0, 1, 2, 3]

theorem m11PS_lt : ∀ p ∈ m11PS, p < 11 := by decide

end CFSG.ComponentClassification.RankTwoSporadic.M11
