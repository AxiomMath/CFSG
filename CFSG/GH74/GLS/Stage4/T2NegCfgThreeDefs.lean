module

public import CFSG.GH74.GLS.Stage4.T2SL2Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Factor

variable {F : Type} [Field F]

structure NegFactor (q : ℕ) (g : GL (Fin 2) F) (W V A : SL2 F) : Prop where
  W_sq : W * W = negOne F
  V_sq : V * V = negOne F
  VW : V * W * V⁻¹ = W⁻¹
  T_cyc : IsCyclic ↥(Subgroup.centralizer ({W} : Set (SL2 F)))
  T_card : Nat.card ↥(Subgroup.centralizer ({W} : Set (SL2 F))) = q + 1
  T_cent : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), Y * Y ≠ 1 → ∀ D : SL2 F,
    D * Y = Y * D → D ∈ Subgroup.centralizer ({W} : Set (SL2 F))
  T_inv : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), V * Y * V⁻¹ = Y⁻¹
  A_cent : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), A * slConj g Y * A⁻¹ = Y
  A_sq : A * slConj g A ∈ Subgroup.centralizer ({W} : Set (SL2 F))
  A_V : V * A * slConj g V⁻¹ = negOne F * slConj g A⁻¹

end Factor

section Skel

variable {G : Type} [Group G]

structure NegSkel (C₁ : Subgroup G) (q : ℕ) (z : G) (K₁ K₂ T₁ T₂ : Subgroup G)
    (x₁ x₂ w₁ w₂ s : G) : Prop where
  s_mem : s ∈ C₁
  s_not_mem : s ∉ K₁ ⊔ K₂
  T₁_le : T₁ ≤ K₁
  T₂_le : T₂ ≤ K₂
  T₁_cyc : IsCyclic ↥T₁
  T₂_cyc : IsCyclic ↥T₂
  T₁_card : Nat.card ↥T₁ = q + 1
  T₂_card : Nat.card ↥T₂ = q + 1
  T₁_cent : ∀ y ∈ T₁, y * y ≠ 1 → ∀ d ∈ K₁, d * y = y * d → d ∈ T₁
  T₂_cent : ∀ y ∈ T₂, y * y ≠ 1 → ∀ d ∈ K₂, d * y = y * d → d ∈ T₂
  x₁_mem : x₁ ∈ T₁
  x₂_mem : x₂ ∈ T₂
  x₁_sq : x₁ * x₁ = z
  x₂_sq : x₂ * x₂ = z
  T₁_iff : ∀ k ∈ K₁, k ∈ T₁ ↔ k * x₁ = x₁ * k
  T₂_iff : ∀ k ∈ K₂, k ∈ T₂ ↔ k * x₂ = x₂ * k
  w₁_mem : w₁ ∈ K₁
  w₂_mem : w₂ ∈ K₂
  w₁_sq : w₁ * w₁ = z
  w₂_sq : w₂ * w₂ = z
  w₁_x : w₁ * x₁ * w₁⁻¹ = x₁ * z
  w₂_x : w₂ * x₂ * w₂⁻¹ = x₂ * z
  w₁_inv : ∀ y ∈ T₁, w₁ * y * w₁⁻¹ = y⁻¹
  w₂_inv : ∀ y ∈ T₂, w₂ * y * w₂⁻¹ = y⁻¹
  s_comm₁ : ∀ y ∈ T₁, s * y = y * s
  s_comm₂ : ∀ y ∈ T₂, s * y = y * s
  s_sq : s * s ∈ T₁ ⊔ T₂
  w₀_s : (w₁ * w₂) * s * (w₁ * w₂)⁻¹ = s⁻¹

end Skel

end CFSG.GH74.GLS.Stage4.Rest
