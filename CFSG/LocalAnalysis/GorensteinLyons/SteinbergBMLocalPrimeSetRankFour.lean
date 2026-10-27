module

public import CFSG.Assembly.LargeEvenDefs

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open CFSG.Assembly

@[expose] def localPrimeSetRankFour (X : Type*) [Group X] [Finite X] (M : Subgroup X) :
    Set ℕ :=
  {p | p ∈ LargeEvenBeta 4 X ∧ ∃ B : Subgroup X, LargeEvenIsBmax p B ∧ B ≤ M}

variable {X : Type*} [Group X] [Finite X]

end CFSG.LocalAnalysis.GorensteinLyons
