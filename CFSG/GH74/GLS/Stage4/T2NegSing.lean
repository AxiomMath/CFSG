module

public import CFSG.GH74.GLS.Stage4.T2TSingEq
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage4.T2NegDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG

section Sing

variable {G : Type} [Group G]

theorem T2Four1.w₁_inv_H₁ {C₁ : Subgroup G} {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}
    (h : T2Four1 C₁ z u K₁ K₂ H w₁ w₂) : ∀ x ∈ H ⊓ K₁, w₁ * x * w₁⁻¹ = x⁻¹ := by
  intro x hx
  have h1 := h.w₀_inv x hx.1
  have h2 : w₂ * x * w₂⁻¹ = x := by
    rw [← h.K_comm x hx.2 w₂ h.w₂_mem]; group
  calc w₁ * x * w₁⁻¹ = w₁ * (w₂ * x * w₂⁻¹) * w₁⁻¹ := by rw [h2]
    _ = (w₁ * w₂) * x * (w₁ * w₂)⁻¹ := by group
    _ = x⁻¹ := h1

theorem T2Four1.w₁_cent_H₂ {C₁ : Subgroup G} {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}
    (h : T2Four1 C₁ z u K₁ K₂ H w₁ w₂) : ∀ x ∈ H ⊓ K₂, w₁ * x * w₁⁻¹ = x := by
  intro x hx
  rw [h.K_comm w₁ h.w₁_mem x hx.2]; group

end Sing

section Main

variable {G : Type} [Group G] [Finite G]

theorem t5_singular_neg {C₁ : Subgroup G} {q : ℕ} {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ a : G}
    (cfg : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) (h3 : 3 ∣ q + 1)
    (haN : a ∈ normalizer (H : Set G)) (ha3 : a ^ 3 ∈ H)
    (hw₁a : ∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) :
    ∃ y : G, (y ∈ H ⊓ K₁ ∨ y ∈ H ⊓ K₂) ∧ y ∉ Subgroup.zpowers z ∧ orderOf y = 3 ∧
      a * y * a⁻¹ = y := by
  have hHc := cfg.H_comm
  have hc1 : Nat.card ↥(H ⊓ K₁) = q + 1 := cfg.H₁_card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x₁, hx₁⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ K₁)) 3 (by rw [hc1]; exact h3)
  have hx₁H : (x₁ : G) ∈ H := x₁.2.1
  have hx₁ord : orderOf (x₁ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx₁
  have hx₁1 : (x₁ : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₁ord
    omega
  have hx₁3 : (x₁ : G) ^ 3 = 1 := by rw [← hx₁ord]; exact pow_orderOf_eq_one _
  have haH : ∀ x ∈ H, a * x * a⁻¹ ∈ H := fun x hx => (Subgroup.mem_normalizer_iff.1 haN x).1 hx
  have hwH : ∀ x ∈ H, w₁ * x * w₁⁻¹ ∈ H := cfg.w₁_normH
  have hw2 : w₁ * w₁ ∈ H := by rw [cfg.w₁_sq]; exact cfg.z_mem_H
  obtain ⟨x₀, hx₀H, hx₀1, hx₀3, hax₀⟩ := t5_fixed hHc haH ha3 hx₁H hx₁1 hx₁3
  obtain ⟨h₀, hh₀, hwa⟩ := hw₁a
  obtain ⟨y, hyH, hy1, hy3, hay, hσ⟩ := t5_split hHc hwH hw2 hh₀ hwa hx₀H hx₀1 hx₀3 hax₀
  obtain ⟨hl₂, hl₁⟩ := t5_loc hHc (inf_le_left : H ⊓ K₁ ≤ H) (inf_le_left : H ⊓ K₂ ≤ H)
    cfg.H_idx cfg.w₁_inv_H₁ cfg.w₁_cent_H₂ hyH hy3
  have hyord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact cfg.zz) cfg.z_ne
  have hyz : y ∉ Subgroup.zpowers z := by
    intro hmem
    have h5 := Subgroup.orderOf_dvd_natCard _ hmem
    rw [Nat.card_zpowers, hz2, hyord] at h5
    omega
  refine ⟨y, ?_, hyz, hyord, hay⟩
  rcases hσ with hs | hs
  · exact Or.inr (hl₂ hs)
  · exact Or.inl (hl₁ hs)

end Main

end CFSG.GH74.GLS.Stage4.Rest
