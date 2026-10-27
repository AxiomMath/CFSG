module

public import CFSG.CGT.Foote81L6.TStruct.E64

public section

namespace CFSG.CGT.Foote81L6

open Subgroup

theorem inv_mul_mem_of_card_eq_two_mul {G : Type*} [Group G] {R V : Subgroup G} [Finite R]
    (hVR : V ≤ R) (hcard : Nat.card R = 2 * Nat.card V) {x y : G} (hx : x ∈ R) (hy : y ∈ R)
    (hxV : x ∉ V) (hyV : y ∉ V) : x⁻¹ * y ∈ V := by
  have hidx : (V.subgroupOf R).index = 2 := by
    have h := card_mul_index (V.subgroupOf R)
    rw [Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv, hcard] at h
    have hV0 : 0 < Nat.card V := by
      rcases Nat.eq_zero_or_pos (Nat.card V) with h0 | h0
      · rw [h0, mul_zero] at hcard
        exact absurd hcard (Nat.card_pos (α := R)).ne'
      · exact h0
    nlinarith
  have := (mul_mem_iff_of_index_two hidx (a := ⟨x⁻¹, inv_mem hx⟩) (b := ⟨y, hy⟩)).2 (by
    rw [mem_subgroupOf, mem_subgroupOf]
    exact ⟨fun h => absurd (inv_inv x ▸ inv_mem h) hxV, fun h => absurd h hyV⟩)
  rw [mem_subgroupOf] at this
  exact this

theorem eq_one_or_eq_of_fix_four {G : Type*} [Group G] {V : Subgroup G}
    (hV2 : ∀ v ∈ V, v * v = 1) (hV4 : Nat.card V = 4) {z g : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (hgz : g * z * g⁻¹ = z) (hmove : ∃ v ∈ V, g * v * g⁻¹ ≠ v) {r : G} (hr : r ∈ V)
    (hgr : g * r * g⁻¹ = r) : r = 1 ∨ r = z := by
  have hz2 : z * z = 1 := hV2 z hz
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  set Z : Subgroup G := zpowers z
  have hZ : ∀ {v : G}, v ∈ Z ↔ v = 1 ∨ v = z := by
    intro v
    constructor
    · intro hv
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
      rw [zpow_eq_zpow_emod' j (show z ^ 2 = 1 by rw [sq]; exact hz2)]
      rcases Int.emod_two_eq_zero_or_one j with h0 | h1
      · left; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h0, zpow_zero]
      · right; rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h1, zpow_one]
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact mem_zpowers _
  have hZV : Z ≤ V := zpowers_le.2 hz
  have hcardZ : Nat.card Z = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  by_contra hcon
  have hrZ : r ∉ Z := fun h => hcon (hZ.1 h)
  obtain ⟨v, hv, hgv⟩ := hmove
  have hvZ : v ∉ Z := by
    intro h
    rcases hZ.1 h with rfl | rfl
    · exact hgv (by group)
    · exact hgv hgz
  have hrv := inv_mul_mem_of_card_eq_two_mul hZV (by rw [hV4, hcardZ]) hr hv hrZ hvZ
  apply hgv
  have hv' : v = r * (r⁻¹ * v) := by group
  rcases hZ.1 hrv with h | h
  · rw [hv', h, mul_one, hgr]
  · rw [hv', h]
    calc g * (r * z) * g⁻¹ = (g * r * g⁻¹) * (g * z * g⁻¹) := by group
      _ = r * z := by rw [hgr, hgz]

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem conj_decomp_B₀ {β α r₀ r₁ : G} (hβ : β ∈ D.B₀) (hα : α ∈ D.A) (hr₁ : r₁ ∈ D.B₁) :
    β * (α * (r₀ * r₁)) * β⁻¹ = α * ((β * r₀ * β⁻¹) * r₁) := by
  have e1 : α * β = β * α := D.A_comm_B α hα β (D.B₀_le_B hβ)
  have e2 : β * r₁ = r₁ * β := D.B₀_comm_B₁ β hβ r₁ hr₁
  calc β * (α * (r₀ * r₁)) * β⁻¹ = (β * α) * r₀ * r₁ * β⁻¹ := by group
    _ = α * β * r₀ * r₁ * β⁻¹ := by rw [e1]
    _ = α * (β * r₀ * β⁻¹) * (β * r₁) * β⁻¹ := by group
    _ = α * (β * r₀ * β⁻¹) * (r₁ * β) * β⁻¹ := by rw [e2]
    _ = α * ((β * r₀ * β⁻¹) * r₁) := by group

theorem conj_decomp_B₁ {β α r₀ r₁ : G} (hβ : β ∈ D.B₁) (hα : α ∈ D.A) (hr₀ : r₀ ∈ D.B₀) :
    β * (α * (r₀ * r₁)) * β⁻¹ = α * (r₀ * (β * r₁ * β⁻¹)) := by
  have e1 : α * β = β * α := D.A_comm_B α hα β (D.B₁_le_B hβ)
  have e2 : r₀ * β = β * r₀ := D.B₀_comm_B₁ r₀ hr₀ β hβ
  calc β * (α * (r₀ * r₁)) * β⁻¹ = (β * α) * r₀ * r₁ * β⁻¹ := by group
    _ = α * β * r₀ * r₁ * β⁻¹ := by rw [e1]
    _ = α * (β * r₀) * r₁ * β⁻¹ := by group
    _ = α * (r₀ * β) * r₁ * β⁻¹ := by rw [e2]
    _ = α * (r₀ * (β * r₁ * β⁻¹)) := by group

theorem eq_one_or_b₀_of_fix_E64 {E : Subgroup G} (hE : IsE64 T E) {β r : G} (hβ : β ∈ D.B₀)
    (hmove : ∃ v ∈ E, β * v * β⁻¹ ≠ v) (hr : r ∈ E ⊓ D.B₀) (hfix : β * r * β⁻¹ = r) :
    r = 1 ∨ r = D.b₀ := by
  have hfour := (D.E64_decomp hE).2.2.1
  refine eq_one_or_eq_of_fix_four hfour.2.1 hfour.2.2 (mem_inf.2 ⟨D.b₀_mem_E64 hE, D.b₀_mem⟩)
    D.b₀_ne_one (by rw [D.b₀_comm β hβ, mul_inv_cancel_right]) ?_ hr hfix
  obtain ⟨v, hv, hmv⟩ := hmove
  obtain ⟨α, hα, v₀, hv₀, v₁, hv₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  refine ⟨v₀, hv₀, fun h => hmv ?_⟩
  rw [D.conj_decomp_B₀ hβ (mem_inf.1 hα).2 (mem_inf.1 hv₁).2, h]

theorem eq_one_or_b₁_of_fix_E64 {E : Subgroup G} (hE : IsE64 T E) {β r : G} (hβ : β ∈ D.B₁)
    (hmove : ∃ v ∈ E, β * v * β⁻¹ ≠ v) (hr : r ∈ E ⊓ D.B₁) (hfix : β * r * β⁻¹ = r) :
    r = 1 ∨ r = D.b₁ := by
  have hfour := (D.E64_decomp hE).2.2.2
  refine eq_one_or_eq_of_fix_four hfour.2.1 hfour.2.2 (mem_inf.2 ⟨D.b₁_mem_E64 hE, D.b₁_mem⟩)
    D.b₁_ne_one (by rw [D.b₁_comm β hβ, mul_inv_cancel_right]) ?_ hr hfix
  obtain ⟨v, hv, hmv⟩ := hmove
  obtain ⟨α, hα, v₀, hv₀, v₁, hv₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  refine ⟨v₁, hv₁, fun h => hmv ?_⟩
  rw [D.conj_decomp_B₁ hβ (mem_inf.1 hα).2 (mem_inf.1 hv₀).2, h]

end FooteCore

end CFSG.CGT.Foote81L6
