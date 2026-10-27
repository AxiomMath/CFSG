module

public import Mathlib.GroupTheory.Index

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open scoped Pointwise

universe v

variable {I : Type v} [Group I]

@[expose] def subgroupCosetInclusion (K H : Subgroup I) : H ⧸ K.subgroupOf H ↪ I ⧸ K where
  toFun := Quotient.map' (fun x : H => (x : I)) fun x y h => by
    rw [QuotientGroup.leftRel_apply] at h ⊢
    exact h
  inj' := Quotient.ind₂' <| by
    intro x y h
    apply QuotientGroup.eq.mpr
    have h' : (QuotientGroup.mk (x : I) : I ⧸ K) = QuotientGroup.mk (y : I) := h
    change (x : I)⁻¹ * (y : I) ∈ K
    exact (QuotientGroup.eq (s := K) (a := (x : I)) (b := (y : I))).mp h'

@[simp] theorem subgroupCosetInclusion_mk (K H : Subgroup I) (x : H) :
    subgroupCosetInclusion K H (QuotientGroup.mk x) = QuotientGroup.mk (x : I) := rfl

theorem subgroupCosetInclusion_range (K H : Subgroup I) :
    Set.range (subgroupCosetInclusion K H) =
      (QuotientGroup.mk : I → I ⧸ K) '' (H : Set I) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Quotient.inductionOn'
    case h x => exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨QuotientGroup.mk (⟨x, hx⟩ : H), rfl⟩

theorem subgroup_coset_image_card (K H : Subgroup I) :
    Nat.card ((QuotientGroup.mk : I → I ⧸ K) '' (H : Set I)) = K.relIndex H := by
  rw [← subgroupCosetInclusion_range]
  exact (Nat.card_congr (Equiv.ofInjective (subgroupCosetInclusion K H)
    (subgroupCosetInclusion K H).injective)).symm

theorem subgroup_product_card (K H : Subgroup I) :
    Nat.card ((H : Set I) * (K : Set I)) = Nat.card K * K.relIndex H := by
  rw [K.card_mul_eq_card_subgroup_mul_card_quotient, subgroup_coset_image_card]

theorem subgroup_product_cover_of_index_eq [Finite I] (K H : Subgroup I)
    (hindex : K.index = K.relIndex H) (x : I) :
    ∃ c ∈ H, ∃ k ∈ K, x = c * k := by
  have hcards : Nat.card (H ⧸ K.subgroupOf H) = Nat.card (I ⧸ K) := hindex.symm
  let e : H ⧸ K.subgroupOf H ≃ I ⧸ K := Classical.choice (Finite.card_eq.mp hcards)
  have hsurj : Function.Surjective (subgroupCosetInclusion K H) :=
    (Finite.injective_iff_surjective_of_equiv e).1 (subgroupCosetInclusion K H).injective
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk x)
  obtain ⟨c, hc⟩ := Quotient.exists_rep q
  rw [← hc] at hq
  have hcx : (c : I)⁻¹ * x ∈ K := QuotientGroup.eq.mp hq
  exact ⟨c, c.property, (c : I)⁻¹ * x, hcx, by simp⟩

theorem relative_index_eq_of_product_cover [Finite I] (K E H : Subgroup I)
    (hEH : E ≤ H) (hcover : ∀ x ∈ H, ∃ e ∈ E, ∃ k ∈ K, x = e * k) :
    K.relIndex H = K.relIndex E := by
  let f := Subgroup.quotientSubgroupOfEmbeddingOfLE K hEH
  have hsurj : Function.Surjective f := by
    intro q
    induction q using Quotient.inductionOn'
    case h x =>
      obtain ⟨e, he, k, hk, hx⟩ := hcover x x.property
      refine ⟨QuotientGroup.mk (⟨e, he⟩ : E), ?_⟩
      apply QuotientGroup.eq.mpr
      change e⁻¹ * (x : I) ∈ K
      rw [hx]
      simpa only [inv_mul_cancel_left] using hk
  exact (Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hsurj⟩)).symm

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
