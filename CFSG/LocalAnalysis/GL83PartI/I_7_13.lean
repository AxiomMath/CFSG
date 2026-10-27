module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace GL83

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def I_7_13_1 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
      CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1 ∧
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

end GL83
