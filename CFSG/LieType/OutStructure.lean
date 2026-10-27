module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OuterPElementLifts (K : Type) [Group K] [Finite K] (p : ℕ) : Prop :=
  ∀ y : Outer K, (∃ k : ℕ, orderOf y = p ^ k) →
    ∃ f : MulAut K, QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K) f = y ∧
      orderOf f = orderOf y

@[expose] def I_7_13_2_5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
        (¬ p ∣ Nat.card (Outer K)) ∨
        (∃ F : Subgroup (MulAut K), (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
          ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
          ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) ∨
        (p = 3 ∧ IsCyclic (Outer K) ∧ OuterPElementLifts K p)

end CFSG.LieType.OutStructure
