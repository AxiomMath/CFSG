module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiHyp43

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)

@[expose] def GomiBenderSL2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], GomiHyp43Type K →
    CFSG.Open.fusionIsBenderGroup (K ⧸ Subgroup.center K) → ∃ m : ℕ, 2 ≤ m ∧ IsSLn K 2 m

end CFSG.GroupTheory
