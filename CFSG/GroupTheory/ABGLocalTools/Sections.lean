module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

open Subgroup
open scoped Pointwise

namespace CFSG.ABGLocalTools

variable {G : Type*} [Group G]

@[expose] def Covers (H X Y : Subgroup G) : Prop :=
  (X : Set G) ⊆ (H : Set G) * (Y : Set G)

@[expose] def IncidentSections (H₁ K₁ H₂ K₂ : Subgroup G) : Prop :=
  (H₁ ⊓ H₂) ⊔ K₁ = H₁ ∧ (H₁ ⊓ H₂) ⊔ K₂ = H₂ ∧ H₁ ⊓ K₂ ≤ K₁ ∧ H₂ ⊓ K₁ ≤ K₂

theorem covers_iff {H X Y : Subgroup G} (hYX : Y ≤ X) (hXY : X ≤ normalizer (Y : Set G)) :
    Covers H X Y ↔ (H ⊓ X) ⊔ Y = X := by
  constructor
  · intro h
    apply le_antisymm (sup_le inf_le_right hYX)
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h hx
    have haX : a ∈ X := by
      have : a = a * b * b⁻¹ := by group
      rw [this]
      exact X.mul_mem hx (X.inv_mem (hYX hb))
    exact Subgroup.mul_mem_sup ⟨ha, haX⟩ hb
  · intro h x hx
    rw [← h] at hx
    have hle : H ⊓ X ≤ normalizer (Y : Set G) := inf_le_right.trans hXY
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, ha.1, b, hb, rfl⟩

theorem permutable_coprime_inf_normal [Finite G] {X Y N : Subgroup G} [N.Normal]
    (hXY : (X : Set G) * Y = Y * X) (hcop : Nat.Coprime (Nat.card X) (Nat.card Y)) :
    (X : Set G) * ((Y ⊓ N : Subgroup G) : Set G) = ((Y ⊓ N : Subgroup G) : Set G) * X ∧
      (X ⊓ N = ⊥ → X ≤ normalizer ((Y ⊓ N : Subgroup G) : Set G)) := by
  have key : ∀ x ∈ X, ∀ y ∈ Y ⊓ N, ∃ y' ∈ Y ⊓ N, ∃ x' ∈ X, x * y = y' * x' := by
    intro x hx y hy
    have hmem : x * y ∈ (Y : Set G) * X := by
      rw [← hXY]
      exact ⟨x, hx, y, hy.1, rfl⟩
    obtain ⟨y', hy', x', hx', hxy⟩ := hmem
    change y' * x' = x * y at hxy
    refine ⟨y', ⟨hy', ?_⟩, x', hx', hxy.symm⟩
    have hy1 : QuotientGroup.mk' N y = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy.2
    have hq : QuotientGroup.mk' N y' = QuotientGroup.mk' N (x * x'⁻¹) := by
      have e : y' = x * y * x'⁻¹ := by rw [← hxy]; group
      rw [e]
      simp only [map_mul, hy1, mul_one]
    have h1 : orderOf (QuotientGroup.mk' N y') ∣ Nat.card Y :=
      (orderOf_map_dvd _ y').trans (Subgroup.orderOf_dvd_natCard Y hy')
    have h2 : orderOf (QuotientGroup.mk' N y') ∣ Nat.card X := by
      rw [hq]
      exact (orderOf_map_dvd _ _).trans
        (Subgroup.orderOf_dvd_natCard X (X.mul_mem hx (X.inv_mem hx')))
    have h3 : orderOf (QuotientGroup.mk' N y') = 1 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  have hsub : (X : Set G) * ((Y ⊓ N : Subgroup G) : Set G) ⊆
      ((Y ⊓ N : Subgroup G) : Set G) * X := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨y', hy', x', hx', h⟩ := key x hx y hy
    exact ⟨y', hy', x', hx', h.symm⟩
  refine ⟨Set.Subset.antisymm hsub ?_, ?_⟩
  · rintro _ ⟨y, hy, x, hx, rfl⟩
    obtain ⟨y', hy', x', hx', h⟩ := key x⁻¹ (X.inv_mem hx) y⁻¹ ((Y ⊓ N).inv_mem hy)
    refine ⟨x'⁻¹, X.inv_mem hx', y'⁻¹, (Y ⊓ N).inv_mem hy', ?_⟩
    have := congrArg (·⁻¹) h
    simp only [mul_inv_rev, inv_inv] at this
    exact this.symm
  · intro hXN x hx
    have hconj : ∀ x ∈ X, ∀ y ∈ Y ⊓ N, x * y * x⁻¹ ∈ Y ⊓ N := by
      intro x hx y hy
      obtain ⟨y', hy', x', hx', h⟩ := key x hx y hy
      have hx'x : x' * x⁻¹ ∈ X ⊓ N := by
        refine ⟨X.mul_mem hx' (X.inv_mem hx), ?_⟩
        have e : x' * x⁻¹ = y'⁻¹ * (x * y * x⁻¹) := by
          have hx'' : x' = y'⁻¹ * (x * y) := by rw [h]; group
          rw [hx'']
          group
        rw [e]
        exact N.mul_mem (N.inv_mem hy'.2) ((inferInstance : N.Normal).conj_mem y hy.2 x)
      rw [hXN, Subgroup.mem_bot, mul_inv_eq_one] at hx'x
      have : x * y * x⁻¹ = y' := by rw [h, hx'x]; group
      rw [this]
      exact hy'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hconj x hx y
    · intro hy
      have := hconj x⁻¹ (X.inv_mem hx) _ hy
      simpa [mul_assoc] using this

theorem covers_of_incident {H H₁ K₁ H₂ K₂ : Subgroup G} (hK₁ : K₁ ≤ H₁) (_hK₂ : K₂ ≤ H₂)
    (_hK₁n : H₁ ≤ normalizer (K₁ : Set G)) (hK₂n : H₂ ≤ normalizer (K₂ : Set G))
    (hinc : IncidentSections H₁ K₁ H₂ K₂) (hcov : Covers H H₁ K₁) (h₁₂ : H₁ ≤ H₂) :
    Covers H H₂ K₂ := by
  obtain ⟨-, h2, -, h4⟩ := hinc
  rw [inf_eq_left.mpr h₁₂] at h2
  intro x hx
  rw [← h2, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (h₁₂.trans hK₂n)] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨h, hh, k, hk, rfl⟩ := hcov ha
  have hkK₂ : k ∈ K₂ := h4 ⟨h₁₂ (hK₁ hk), hk⟩
  exact ⟨h, hh, k * b, K₂.mul_mem hkK₂ hb, (mul_assoc h k b).symm⟩

theorem incident_of_le_of_relIndex_eq [Finite G] {H₁ K₁ H₂ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ H₁) (hK₂ : K₂ ≤ H₂) (_hK₁n : H₁ ≤ normalizer (K₁ : Set G))
    (hK₂n : H₂ ≤ normalizer (K₂ : Set G)) (h₁₂ : H₁ ≤ H₂)
    (hcard : K₁.relIndex H₁ = K₂.relIndex H₂) (hK : K₂ ⊓ H₁ ≤ K₁) :
    IncidentSections H₁ K₁ H₂ K₂ := by
  have hsupH₂ : H₁ ⊔ K₂ ≤ H₂ := sup_le h₁₂ hK₂
  have hnormal : (K₂.subgroupOf H₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂).mpr hK₂n
  have hsup : K₂.relIndex (H₁ ⊔ K₂) = K₂.relIndex H₁ := by
    have := Subgroup.relIndex_sup_right (H := H₁.subgroupOf H₂) (K := K₂.subgroupOf H₂)
    rwa [← Subgroup.subgroupOf_sup h₁₂ hK₂, Subgroup.relIndex_subgroupOf hsupH₂,
      Subgroup.relIndex_subgroupOf h₁₂] at this
  have htower₁ := Subgroup.relIndex_mul_relIndex K₂ (H₁ ⊔ K₂) H₂ le_sup_right hsupH₂
  have htower₂ := Subgroup.relIndex_mul_relIndex (K₂ ⊓ H₁) K₁ H₁ hK hK₁
  rw [← Subgroup.inf_relIndex_right K₂ H₁] at hsup
  rw [hsup, ← htower₂, ← hcard] at htower₁
  have hpos : 0 < K₁.relIndex H₁ := by
    have h := Subgroup.relIndex_mul_card K₁ H₁
    apply Nat.pos_of_ne_zero
    intro h0
    rw [h0, zero_mul] at h
    exact Nat.card_pos.ne' h.symm
  have hone : (K₂ ⊓ H₁).relIndex K₁ * (H₁ ⊔ K₂).relIndex H₂ = 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [one_mul]
    calc (K₂ ⊓ H₁).relIndex K₁ * (H₁ ⊔ K₂).relIndex H₂ * K₁.relIndex H₁
        = (K₂ ⊓ H₁).relIndex K₁ * K₁.relIndex H₁ * (H₁ ⊔ K₂).relIndex H₂ := by ring
      _ = K₁.relIndex H₁ := htower₁
  have hi₁ : (K₂ ⊓ H₁).relIndex K₁ = 1 := Nat.eq_one_of_mul_eq_one_right hone
  have hi₂ : (H₁ ⊔ K₂).relIndex H₂ = 1 := Nat.eq_one_of_mul_eq_one_left hone
  rw [Subgroup.relIndex_eq_one] at hi₁ hi₂
  have hK₁K₂ : K₁ ≤ K₂ := hi₁.trans inf_le_left
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [inf_eq_left.mpr h₁₂]
    exact sup_eq_left.mpr hK₁
  · rw [inf_eq_left.mpr h₁₂]
    exact le_antisymm hsupH₂ hi₂
  · rw [inf_comm]
    exact hK
  · exact inf_le_right.trans hK₁K₂

theorem incident_of_le_of_mulEquiv [Finite G] {H₁ K₁ H₂ K₂ : Subgroup G}
    (hK₁ : K₁ ≤ H₁) (hK₂ : K₂ ≤ H₂) [(K₁.subgroupOf H₁).Normal] [hn : (K₂.subgroupOf H₂).Normal]
    (h₁₂ : H₁ ≤ H₂) (e : H₁ ⧸ K₁.subgroupOf H₁ ≃* H₂ ⧸ K₂.subgroupOf H₂) (hK : K₂ ⊓ H₁ ≤ K₁) :
    IncidentSections H₁ K₁ H₂ K₂ := by
  have hK₁n : H₁ ≤ normalizer (K₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₁).mp inferInstance
  have hK₂n : H₂ ≤ normalizer (K₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₂).mp hn
  exact incident_of_le_of_relIndex_eq hK₁ hK₂ hK₁n hK₂n h₁₂ (Nat.card_congr e.toEquiv) hK

end CFSG.ABGLocalTools
