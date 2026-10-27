module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

@[expose] def sec6Piece {X : Type} [Group X] (L : Subgroup X) (b : X) : Subgroup X :=
  oTwoPrimeOf (L ⊓ cen b)

structure Sec6CtrlAt (X : Type) [Group X] (n : ℕ) (t : X) : Prop where
  land : ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ L : Subgroup X, Sec6KComp X n (cen t) L →
      ∃ F : Subgroup X, Sec6KComp X n (cen b) F ∧ sec6Piece L b ≤ F
  piece : ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ F : Subgroup X, Sec6KComp X n (cen b) F →
      ∃ L : Subgroup X, Sec6KComp X n (cen t) L ∧ sec6Piece L b ≤ F
  dich : ∀ b ∈ Sec6M X n (cen t) ⊔ Sec6Q X n (cen t), orderOf b = 2 →
    ∀ L F : Subgroup X, Sec6KComp X n (cen t) L → Sec6KComp X n (cen b) F → sec6Piece L b ≤ F →
      t ∈ normalizer (F : Set X) ∧
        (F = oddCoreOf F ⊔ sec6Piece L b ∨
          (Sec6MComp X n (cen b) F ∧ ¬ CentModOdd F t ∧ ∃ f ∈ F, CentModOdd F (f * t)))

@[expose] def Sec6CtrlHolds : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ) (t : X), Sec6Setting X n t → Sec6Lemma51 X n →
    (∀ x ∈ Sec6Q X n (cen t), orderOf x = 2 → Sec6Covers X n t x) → Sec6CtrlAt X n t

end CFSG.OddStandard.Solomon75
