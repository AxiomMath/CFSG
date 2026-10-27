module

public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.EvenSporadicStandard.M24Std.Thirteen

open Subgroup

variable {G : Type*} [Group G]

theorem card_mul_card_le_of_const {S T U : Set G} [Finite S] (τ : G → G)
    (hT : ∀ t ∈ T, ∃ s ∈ S, τ s = t) (hU : ∀ s ∈ S, ∀ u ∈ U, s * u ∈ S ∧ τ (s * u) = τ s) :
    Nat.card T * Nat.card U ≤ Nat.card S := by
  choose σ hσS hστ using hT
  let F : T × U → S := fun p => ⟨σ p.1 p.1.2 * p.2, (hU _ (hσS _ p.1.2) _ p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨⟨t, ht⟩, ⟨u, hu⟩⟩ ⟨⟨t', ht'⟩, ⟨u', hu'⟩⟩ h
    have h' : σ t ht * u = σ t' ht' * u' := congrArg Subtype.val h
    have htt : t = t' := by
      rw [← hστ t ht, ← hστ t' ht', ← (hU _ (hσS t ht) u hu).2, ← (hU _ (hσS t' ht') u' hu').2,
        h']
    subst htt
    have huu : u = u' := mul_left_cancel h'
    subst huu
    rfl
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective F hF

theorem subset_of_card_le [Finite G] {S T U : Set G} (τ : G → G)
    (hT : ∀ t ∈ T, ∃ s ∈ S, τ s = t) (hU : ∀ s ∈ S, ∀ u ∈ U, s * u ∈ S ∧ τ (s * u) = τ s)
    (hTU : T ⊆ U) (hS : Nat.card S ≤ Nat.card T * Nat.card T) (hT0 : 0 < Nat.card T) :
    U ⊆ T := by
  have h1 := card_mul_card_le_of_const τ hT hU
  have h2 : Nat.card U ≤ Nat.card T := Nat.le_of_mul_le_mul_left (h1.trans hS) hT0
  exact (Set.eq_of_subset_of_ncard_le hTU h2).symm.subset

def mulMapOf {H K S : Set G} (hmul : ∀ h ∈ H, ∀ k ∈ K, h * k ∈ S) : H × K → S :=
  fun p => ⟨p.1 * p.2, hmul _ p.1.2 _ p.2.2⟩

theorem mulMapOf_injective {H K S : Set G} (hmul : ∀ h ∈ H, ∀ k ∈ K, h * k ∈ S)
    (hinj : ∀ h ∈ H, ∀ h' ∈ H, ∀ k ∈ K, ∀ k' ∈ K, h * k = h' * k' → h = h') :
    Function.Injective (mulMapOf hmul) := by
  rintro ⟨⟨h, hh⟩, ⟨k, hk⟩⟩ ⟨⟨h', hh'⟩, ⟨k', hk'⟩⟩ e
  have e' : h * k = h' * k' := congrArg Subtype.val e
  have hhh : h = h' := hinj h hh h' hh' k hk k' hk' e'
  subst hhh
  have hkk : k = k' := mul_left_cancel e'
  subst hkk
  rfl

theorem card_mul_card_le_of_inj {H K S : Set G} [Finite S]
    (hmul : ∀ h ∈ H, ∀ k ∈ K, h * k ∈ S)
    (hinj : ∀ h ∈ H, ∀ h' ∈ H, ∀ k ∈ K, ∀ k' ∈ K, h * k = h' * k' → h = h') :
    Nat.card H * Nat.card K ≤ Nat.card S := by
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective _ (mulMapOf_injective hmul hinj)

theorem exists_mul_eq_of_card_le {H K S : Set G} [Finite S]
    (hmul : ∀ h ∈ H, ∀ k ∈ K, h * k ∈ S)
    (hinj : ∀ h ∈ H, ∀ h' ∈ H, ∀ k ∈ K, ∀ k' ∈ K, h * k = h' * k' → h = h')
    (hcard : Nat.card S ≤ Nat.card H * Nat.card K) :
    ∀ s ∈ S, ∃ h ∈ H, ∃ k ∈ K, s = h * k := by
  have hb := (mulMapOf_injective hmul hinj).bijective_of_nat_card_le
    (by rw [Nat.card_prod]; exact hcard)
  intro s hs
  obtain ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, he⟩ := hb.2 ⟨s, hs⟩
  exact ⟨h, hh, k, hk, (congrArg Subtype.val he).symm⟩

theorem card_le_add_of_forall [Finite G] {K T C : Subgroup G}
    (hKT : ∀ k ∈ K, k ∈ C → k ∈ T) (hK : ∀ k ∈ K, ∀ k' ∈ K, k ∉ C → k' ∉ C → k⁻¹ * k' ∈ C) :
    Nat.card K ≤ Nat.card T + Nat.card T := by
  by_cases h : ∃ k₀ ∈ K, k₀ ∉ C
  · obtain ⟨k₀, hk₀K, hk₀C⟩ := h
    have hsub : (K : Set G) ⊆ (T : Set G) ∪ (fun g => k₀ * g) '' (T : Set G) := by
      intro k hk
      by_cases hkC : k ∈ C
      · exact Or.inl (hKT k hk hkC)
      · refine Or.inr ⟨k₀⁻¹ * k, hKT _ (K.mul_mem (K.inv_mem hk₀K) hk)
          (hK _ hk₀K _ hk hk₀C hkC), ?_⟩
        simp only [mul_inv_cancel_left]
    calc Nat.card K = (K : Set G).ncard := rfl
      _ ≤ ((T : Set G) ∪ (fun g => k₀ * g) '' (T : Set G)).ncard := Set.ncard_le_ncard hsub
      _ ≤ (T : Set G).ncard + ((fun g => k₀ * g) '' (T : Set G)).ncard := Set.ncard_union_le _ _
      _ = Nat.card T + Nat.card T := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective k₀)]
        rfl
  · push Not at h
    exact (Subgroup.card_le_of_le fun k hk => hKT k hk (h k hk)).trans (Nat.le_add_right _ _)

theorem nonempty_of_closure_eq {S : Set G} {Z : Subgroup G} (h : closure S = Z)
    (hZ : Nat.card Z ≠ 1) : S.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  rw [Subgroup.closure_empty] at h
  rw [← h, card_bot] at hZ
  exact hZ rfl

end CFSG.EvenSporadicStandard.M24Std.Thirteen
