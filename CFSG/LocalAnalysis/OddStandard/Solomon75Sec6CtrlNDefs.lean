module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

structure Sec6CtrlNAt (X : Type) [Group X] (n : ℕ) (t : X) (N : Subgroup X) : Prop where
  norm : ∀ F : Subgroup X, Sec6KComp X n N F → t ∈ normalizer (F : Set X)
  piece : ∀ F : Subgroup X, Sec6KComp X n N F →
    ∃ L : Subgroup X, Sec6KComp X n (cen t) L ∧ L ≤ F
  dich : ∀ L F : Subgroup X, Sec6KComp X n (cen t) L → Sec6KComp X n N F → L ≤ F →
    F = oddCoreOf F ⊔ L ∨
      (Sec6MComp X n N F ∧ Sec5Comp X n (cen t) L ∧ ¬ CentModOdd F t ∧
        ∃ f ∈ F, CentModOdd F (f * t))

end CFSG.OddStandard.Solomon75
