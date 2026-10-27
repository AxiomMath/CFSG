module

public import CFSG.GH74.GLS.Stage4.T2NegDefs
public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeDefs
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.T2
open scoped Pointwise commutatorElement

section Cfg

variable {G : Type} [Group G]

structure Ch6MixCfg (C₁ : Subgroup G) (q₁ q₂ : ℕ) (z u : G) (K₁ K₂ H : Subgroup G) (w₁ w₂ : G) : Prop
    extends T2Four1 C₁ z u K₁ K₂ H w₁ w₂ where
  H₁_cyc : IsCyclic ↥(H ⊓ K₁)
  H₂_cyc : IsCyclic ↥(H ⊓ K₂)
  H₁_card : Nat.card ↥(H ⊓ K₁) = q₁ + 1
  H₂_card : Nat.card ↥(H ⊓ K₂) = q₂ - 1
  H_idx : ((H ⊓ K₁) ⊔ (H ⊓ K₂)).relIndex H = 2
  H₁_cent : ∀ y ∈ H ⊓ K₁, y * y ≠ 1 → ∀ d ∈ K₁, d * y = y * d → d ∈ H

structure MixCoord2 {F : Type} [Field F] (φ : SL2 F →* G) (z u w₂ : G) (K₂ H : Subgroup G) : Prop where
  inj : Function.Injective φ
  range : φ.range = K₂
  neg : φ (negOne F) = z
  w : w₂ = φ (sl2W F)
  H_inf : H ⊓ K₂ = (tSub F).map φ
  H_norm_u : ∀ h ∈ H, ∀ x ∈ (uSub F).map φ, h * x * h⁻¹ ∈ (uSub F).map φ
  H_norm_l : ∀ h ∈ H, ∀ x ∈ (lSub F).map φ, h * x * h⁻¹ ∈ (lSub F).map φ
  hu : ∀ x, u * φ x * u⁻¹ = φ (slConj (dNeg F) x)

end Cfg

section Factor

variable {F : Type} [Field F]

structure MixFactor (c : ℕ) (g : GL (Fin 2) F) (W V A : SL2 F) : Prop where
  W_sq : W * W = negOne F
  V_sq : V * V = negOne F
  VW : V * W * V⁻¹ = W⁻¹
  T_cyc : IsCyclic ↥(Subgroup.centralizer ({W} : Set (SL2 F)))
  T_card : Nat.card ↥(Subgroup.centralizer ({W} : Set (SL2 F))) = c
  T_cent : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), Y * Y ≠ 1 → ∀ D : SL2 F,
    D * Y = Y * D → D ∈ Subgroup.centralizer ({W} : Set (SL2 F))
  T_inv : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), V * Y * V⁻¹ = Y⁻¹
  A_cent : ∀ Y ∈ Subgroup.centralizer ({W} : Set (SL2 F)), A * slConj g Y * A⁻¹ = Y
  A_sq : A * slConj g A ∈ Subgroup.centralizer ({W} : Set (SL2 F))
  A_V : V * A * slConj g V⁻¹ = negOne F * slConj g A⁻¹

theorem NegFactor.toMix {q : ℕ} {g : GL (Fin 2) F} {W V A : SL2 F} (h : NegFactor q g W V A) :
    MixFactor (q + 1) g W V A :=
  ⟨h.W_sq, h.V_sq, h.VW, h.T_cyc, h.T_card, h.T_cent, h.T_inv, h.A_cent, h.A_sq, h.A_V⟩

end Factor

section Skel

variable {G : Type} [Group G]

structure MixSkel (C₁ : Subgroup G) (c₁ c₂ : ℕ) (z : G) (K₁ K₂ T₁ T₂ : Subgroup G)
    (x₁ x₂ w₁ w₂ s : G) : Prop where
  s_mem : s ∈ C₁
  s_not_mem : s ∉ K₁ ⊔ K₂
  T₁_le : T₁ ≤ K₁
  T₂_le : T₂ ≤ K₂
  T₁_cyc : IsCyclic ↥T₁
  T₂_cyc : IsCyclic ↥T₂
  T₁_card : Nat.card ↥T₁ = c₁
  T₂_card : Nat.card ↥T₂ = c₂
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

structure MixSkelHalf (c : ℕ) (z : G) (K T : Subgroup G) (x w : G) : Prop where
  T_le : T ≤ K
  T_cyc : IsCyclic ↥T
  T_card : Nat.card ↥T = c
  T_cent : ∀ y ∈ T, y * y ≠ 1 → ∀ d ∈ K, d * y = y * d → d ∈ T
  x_mem : x ∈ T
  x_sq : x * x = z
  T_iff : ∀ k ∈ K, k ∈ T ↔ k * x = x * k
  w_mem : w ∈ K
  w_sq : w * w = z
  w_x : w * x * w⁻¹ = x * z
  w_inv : ∀ y ∈ T, w * y * w⁻¹ = y⁻¹

end Skel

end CFSG.GH74.GLS.Stage4.Rest
