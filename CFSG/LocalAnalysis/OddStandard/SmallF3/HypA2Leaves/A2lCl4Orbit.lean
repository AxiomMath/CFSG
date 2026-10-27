module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.SetTheory.Cardinal.NatCard

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

theorem cl24_card_ge_of_invariant {X β : Type*} [Finite X] (c : X → β) (T : X → Set X)
    (hc : ∀ x, ∀ z ∈ T x, c z = c x) (S₀ : Set X) (m : ℕ)
    (hm : ∀ x ∈ S₀, m ≤ Nat.card (T x)) :
    (c '' S₀).ncard * m ≤ Nat.card X := by
  classical
  have hrep : ∀ t : c '' S₀, ∃ x ∈ S₀, c x = (t : β) := fun t => t.2
  choose x hxS hxc using hrep
  have hm' : ∀ t : c '' S₀, m ≤ Nat.card (T (x t)) := fun t => hm _ (hxS t)
  let φ : ∀ t : c '' S₀, Fin m → T (x t) := fun t =>
    (Finite.equivFin (T (x t))).symm ∘ Fin.castLE (hm' t)
  have hφ : ∀ t, Function.Injective (φ t) := fun t =>
    (Equiv.injective _).comp (Fin.castLE_injective _)
  let F : (c '' S₀) × Fin m → X := fun p => (φ p.1 p.2 : X)
  have hF : Function.Injective F := by
    rintro ⟨t, i⟩ ⟨t', i'⟩ h
    have key : ∀ (s : c '' S₀) (j : Fin m), c (φ s j : X) = (s : β) := by
      intro s j
      rw [hc _ _ (φ s j).2, hxc]
    have htt : t = t' := by
      apply Subtype.ext
      rw [← key t i, ← key t' i']
      exact congrArg c h
    subst htt
    have : φ t i = φ t i' := Subtype.ext h
    exact Prod.ext rfl (hφ t this)
  have h1 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
    Nat.card_coe_set_eq] at h1
  exact h1

theorem cl24_card_cover_le {W : Type*} [Finite W] (𝒴 : Set (Set W)) (m : ℕ) (z : W)
    (hY : ∀ Y ∈ 𝒴, z ∈ Y ∧ Y.ncard = m) (Ω : Set W) (hz : z ∉ Ω)
    (hcov : ∀ v ∈ Ω, ∃ Y ∈ 𝒴, v ∈ Y) : Ω.ncard ≤ 𝒴.ncard * (m - 1) := by
  classical
  have hfin : 𝒴.Finite := Set.toFinite _
  have hsub : Ω ⊆ ⋃ Y ∈ 𝒴, (Y \ {z}) := by
    intro v hv
    obtain ⟨Y, hY', hvY⟩ := hcov v hv
    simp only [Set.mem_iUnion]
    exact ⟨Y, hY', hvY, fun h => hz (by rw [Set.mem_singleton_iff.mp h] at hv; exact hv)⟩
  calc Ω.ncard ≤ (⋃ Y ∈ 𝒴, (Y \ {z})).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ᶠ Y ∈ 𝒴, (Y \ {z}).ncard := Set.Finite.ncard_biUnion_le hfin _
    _ = ∑ᶠ Y ∈ 𝒴, (m - 1) := finsum_mem_congr rfl fun Y hY' => by
        rw [Set.ncard_diff_singleton_of_mem (hY Y hY').1, (hY Y hY').2]
    _ = 𝒴.ncard * (m - 1) := by
        rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_const, smul_eq_mul,
          Set.ncard_eq_toFinset_card 𝒴 hfin]

end CFSG.OddStandard.SmallF3.HypA2Leaves
