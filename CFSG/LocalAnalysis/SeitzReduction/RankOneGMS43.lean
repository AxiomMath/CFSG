module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43TheoremA

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

@[expose] def GMS43MasonInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T V₁ U₁ : Subgroup G)
    (y d : G), Goldschmidt1974 → Endings.Setting G L f t T →
    GMS28.Result (zpowers t) L (T ⊓ L) T f t V₁ U₁ y d → (∀ u ∈ U₁, u * u = 1) →
    (∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t) →
    4 ≤ (T ⊓ L ⊔ zpowers t).relIndex T →
    ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ (normalizer (U₁ : Set G)) → U₁ ⊔ T < S₁ →
    ∀ X : Subgroup G, X ≤ S₁ → (∀ x ∈ X, x * x = 1) → ¬ X ≤ U₁ →
      (∀ x ∈ X, ∀ g : G, g⁻¹ * t * g ≠ x) →
      (∀ x ∈ X, Nat.card (⁅U₁, zpowers x⁆ : Subgroup G) ≤ U₁.relIndex X) → False

theorem gms43InvolutionCase_of_masonInput (hM : GMS43MasonInput) :
    Endings.GMS43InvolutionCase := by
  intro G _ _ L f t T V₁ U₁ y d hGold hS hR hel hx
  have h : GMS43.Hyp L f t T V₁ U₁ y d := ⟨hGold, hS, hR, hel⟩
  rcases h.relIndex_eq_two_or_four_le hx with h2 | h4
  · exact h.false_of_relIndex_le_two hx h2.le
  obtain ⟨S, hsyl, hES⟩ := h.exists_isSylowOf_le_normalizer
  rcases eq_or_lt_of_le hES with heq | hlt
  · exact h.false_of_isSylowOf (heq ▸ hsyl)
  refine h.false_of_commutator_bound (le_sup_left.trans hES) hsyl fun U hU g hUS hUE => ?_
  by_contra hall
  push Not at hall
  exact hM G L f t T V₁ U₁ y d hGold hS hR hel hx h4 S hsyl hlt _ hUS
    (h.rightConjugate_mul_self hU g) hUE (h.not_conj_mem_rightConjugate hU g) hall

end CFSG.SeitzReduction.RankOne
