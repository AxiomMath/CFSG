module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Defs

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowAlt

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def RowCore (C : ℕ → (S : Type) → [Group S] → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → C p S →
    ∀ t : S, orderOf t = 2 → ∀ J : Subgroup S, J ≤ centralizer {t} →
    (J.subgroupOf (centralizer {t})).IsSubnormal → t ∈ J → IsTwoQuasisimple ↥J →
    ∀ (L : Type) [Group L] [Finite L], IsMTypeSchur p L → InductionTypeField p L →
      Nonempty (L ⧸ Open.fusionZStar L ≃* ↥J ⧸ Open.fusionZStar ↥J) → False

end CFSG.ComponentClassification.HarrisLit.T1.RowAlt
