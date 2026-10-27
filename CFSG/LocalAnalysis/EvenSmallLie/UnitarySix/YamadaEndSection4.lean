module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndConj
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndDefs
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaEndL44Defs

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaEnd

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint
open scoped MatrixGroups

variable {G : Type} [Group G]

structure YamadaData (G : Type) [Group G] where
  L : Subgroup G
  t : G
  S : Subgroup G
  A₁ : Subgroup G
  A₂ : Subgroup G
  K₁ : Subgroup G
  K₂ : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  X₃ : Subgroup G
  J : Subgroup G
  V₁ : Subgroup G
  D₁ : Subgroup G
  D₂ : Subgroup G
  N₁ : Subgroup G
  N₂ : Subgroup G
  P : Subgroup G
  w₁ : G
  w₂ : G
  w₃ : G

namespace YamadaData

variable (d : YamadaData G)

@[expose] def H : Subgroup G := centralizer ({d.t} : Set G)

@[expose] def w₀ : G := (d.w₁ * d.w₂ * d.w₃) ^ 3

@[expose] def u₁ : G := d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁

@[expose] def u₂ : G := d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ * d.w₃

@[expose] def L₁ : Subgroup G := d.N₁ ⊓ conjR d.N₁ d.u₁

@[expose] def L₂ : Subgroup G := d.N₂ ⊓ conjR d.N₂ d.u₂

@[expose] def P₁ : Subgroup G := d.P ⊓ conjR d.P d.u₁

@[expose] def P₂ : Subgroup G := d.P ⊓ conjR d.P d.u₂

@[expose] def Ua : Subgroup G := d.P₂ ⊓ conjR d.P₂ (d.w₁ * d.w₂)

@[expose] def Ub : Subgroup G := d.P₂ ⊓ conjR d.P₂ (d.w₂ * d.w₁)

@[expose] def Uc : Subgroup G := d.P₁ ⊓ conjR d.P₁ (d.w₂ * d.w₃ * d.w₂)

@[expose] def Ya : Subgroup G := d.Ua ⊔ conjR d.Ua d.w₁

@[expose] def Yb : Subgroup G := d.Ub ⊔ conjR d.Ub d.w₂

@[expose] def Yc : Subgroup G := d.Uc ⊔ conjR d.Uc d.w₃

@[expose] def G₀ : Subgroup G := d.Ya ⊔ d.Yb ⊔ d.Yc

end YamadaData

structure YamadaSection4 (F : Type) [Field F] [Finite F] [CharP F 2] [Finite G]
    (d : YamadaData G) : Prop where
  setting : StandardSetting G d.L
  center_eq : center d.L = ⊥
  lie : LieModel (d.L ⧸ center d.L) .PSU 6 2 1
  card_field : Nat.card F = 4
  order_t : orderOf d.t = 2
  t_mem : d.t ∈ centralizer (d.L : Set G)
  kernel : centralizer (d.L : Set G) ⊓ d.H = zpowers d.t
  sylow : IsSylowOf 2 d.S d.L
  card_normalizer : Nat.card (normalizer (d.S : Set G) ⊓ d.L : Subgroup G) = 2 ^ 15 * 3
  w₁_mem : d.w₁ ∈ d.L
  w₂_mem : d.w₂ ∈ d.L
  w₃_mem : d.w₃ ∈ d.L
  w₁_sq : d.w₁ * d.w₁ = 1
  w₂_sq : d.w₂ * d.w₂ = 1
  w₃_sq : d.w₃ * d.w₃ = 1
  braid : d.w₁ * d.w₂ * d.w₁ = d.w₂ * d.w₁ * d.w₂
  word_a : d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ * d.w₃ * d.w₁ * d.w₂ = d.w₀ * d.w₁
  word_b : d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ = d.w₀ * d.w₂
  word_b' : d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ * d.w₃ * d.w₂ * d.w₃ = d.w₀ * d.w₂
  word_c : d.w₁ * d.w₂ * d.w₃ * d.w₂ * d.w₁ * d.w₂ * d.w₃ * d.w₂ = d.w₀ * d.w₃
  word_c' : d.w₁ * d.w₂ * d.w₁ * d.w₃ * d.w₂ * d.w₃ * d.w₁ * d.w₂ = d.w₀ * d.w₃
  card_X₁ : Nat.card d.X₁ = 4
  card_X₂ : Nat.card d.X₂ = 4
  card_X₃ : Nat.card d.X₃ = 2
  w₁_gen : d.w₁ ∈ d.X₁ ⊔ conjR d.X₁ d.w₁
  w₂_gen : d.w₂ ∈ d.X₂ ⊔ conjR d.X₂ d.w₂
  w₃_gen : d.w₃ ∈ d.X₃ ⊔ conjR d.X₃ d.w₃
  X₂_quasisimple : CFSG.Open.IsQuasisimple (d.X₂ ⊔ conjR d.X₂ d.w₂ : Subgroup G)
  K₁_model : ∃ χ : msigma F ≃* d.K₁,
    (∀ A : msigma F, (A : SL(4, F)) = sY F 0 * sY F 2 → (χ A : G) = d.w₂) ∧
    (∀ A : msigma F, (A : SL(4, F)) = sY F 1 → (χ A : G) = d.w₃) ∧
    ∀ A : msigma F, (A : SL(4, F)) ∈ pstd F → (χ A : G) ∈ d.S ⊓ conjR d.S d.u₁
  K₂_pair : ∃ θ : SL(3, F) →* G, θ.range = d.K₂ ∧ θ.ker = center SL(3, F) ∧
    (CFSG.ClassicalInvolution.WeakCT.B12 F).map θ = d.X₁ ⊔ conjR d.X₁ d.w₁ ∧
    (CFSG.ClassicalInvolution.WeakCT.B23 F).map θ = d.X₂ ⊔ conjR d.X₂ d.w₂
  K₂_lie : LieModel d.K₂ .PSL 3 2 2
  L_gen : d.L ≤ d.X₁ ⊔ d.X₂ ⊔ d.X₃ ⊔ zpowers d.w₁ ⊔ zpowers d.w₂ ⊔ zpowers d.w₃
  K₂_gen : d.K₂ = d.X₁ ⊔ d.X₂ ⊔ zpowers d.w₁ ⊔ zpowers d.w₂
  K₁_gen : d.K₁ = d.X₂ ⊔ d.X₃ ⊔ zpowers d.w₂ ⊔ zpowers d.w₃
  K₁_le : d.K₁ ≤ d.L
  K₂_le : d.K₂ ≤ d.L
  A₁_le : d.A₁ ≤ d.S
  A₂_le : d.A₂ ≤ d.S
  K₁_A₁ : d.K₁ ⊓ d.A₁ = ⊥
  K₂_A₂ : d.K₂ ⊓ d.A₂ = ⊥
  KA₁ : (d.K₁ ⊔ d.A₁) ⊓ conjR (d.K₁ ⊔ d.A₁) d.u₁ = d.K₁
  KA₂ : (d.K₂ ⊔ d.A₂) ⊓ conjR (d.K₂ ⊔ d.A₂) d.u₂ = d.K₂
  S_w₀ : d.S ⊓ conjR d.S d.w₀ = ⊥
  S_a : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₁ * d.w₂) = d.X₁
  S_b : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₂ * d.w₁) = d.X₂
  S_c : (d.S ⊓ conjR d.S d.u₁) ⊓ conjR (d.S ⊓ conjR d.S d.u₁) (d.w₂ * d.w₃ * d.w₂) = d.X₃
  S_aba : (d.S ⊓ conjR d.S d.u₂) ⊓ conjR (d.S ⊓ conjR d.S d.u₂) (d.w₁ * d.w₂ * d.w₁) = ⊥
  card_S₂ : Nat.card (d.S ⊓ conjR d.S d.u₂ : Subgroup G) = 2 ^ 6
  normalizer_center : normalizer (centerSub (d.S ⊔ zpowers d.t) : Set G) =
    (normalizer (d.A₁ : Set G) ⊓ d.H) ⊔ d.V₁
  V₁_normal : normalizer (centerSub (d.S ⊔ zpowers d.t) : Set G) ≤ normalizer (d.V₁ : Set G)
  V₁_sq : ∀ v ∈ d.V₁, v * v = 1
  V₁_fix : d.V₁ ⊓ d.H ≤ d.S
  card_V₁ : Nat.card d.V₁ = 4
  K₁_centralizes : d.K₁ ≤ centralizer (d.V₁ : Set G)
  D₂_comm : ∀ x ∈ d.D₂, ∀ y ∈ d.D₂, x * y = y * x
  D₂_H : d.D₂ ⊓ d.H = d.A₂
  D₂_irred : ∀ E : Subgroup G, d.A₂ ≤ E → E ≤ d.D₂ → d.K₂ ≤ normalizer (E : Set G) →
    E = d.A₂ ∨ E = d.D₂
  V₁_le_D₂ : d.V₁ ≤ d.D₂
  D₁_H : d.D₁ ⊓ d.H = d.A₁
  card_D₁ : Nat.card d.D₁ = 2 ^ 18
  card_D₂ : Nat.card d.D₂ = 2 ^ 18
  D₁_le : d.D₁ ≤ d.N₁
  D₂_le : d.D₂ ≤ d.N₂
  N₁_norm : d.N₁ ≤ normalizer (d.D₁ : Set G)
  N₂_norm : d.N₂ ≤ normalizer (d.D₂ : Set G)
  N₁_H : d.N₁ ⊓ d.H = d.K₁ ⊔ d.A₁
  N₂_H : d.N₂ ⊓ d.H = d.K₂ ⊔ d.A₂
  t_N₁ : d.t ∈ normalizer (d.N₁ : Set G)
  t_N₂ : d.t ∈ normalizer (d.N₂ : Set G)
  t_D₁ : d.t ∈ normalizer (d.D₁ : Set G)
  t_D₂ : d.t ∈ normalizer (d.D₂ : Set G)
  t_P : d.t ∈ normalizer (d.P : Set G)
  normalizer_S : normalizer (d.S : Set G) ⊓ d.H ≤
    normalizer (d.N₁ : Set G) ⊓ normalizer (d.N₂ : Set G)
  centralizer₁ : ∀ x ∈ d.N₁, x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₁ → x ∈ d.K₁ ⊔ d.D₁
  centralizer₂ : ∀ x ∈ d.N₂, x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂ → x ∈ d.K₂ ⊔ d.D₂
  type₁ : (∃ _ : (d.D₁.subgroupOf d.N₁).Normal, ∃ ψ : SL(4, F) →* d.N₁ ⧸ d.D₁.subgroupOf d.N₁,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(4, F)) ∨
    ∃ M : Subgroup G, d.D₁ ≤ M ∧ M ≤ d.N₁ ∧ d.N₁ = M ⊔ conjR M d.t ∧
      ⁅M, conjR M d.t⁆ ≤ d.D₁ ∧ M ⊓ conjR M d.t = d.D₁ ∧
      ∃ _ : (d.D₁.subgroupOf M).Normal, LieModel (M ⧸ d.D₁.subgroupOf M) .PSU 4 2 1
  type₂ : ∃ M : Subgroup G, d.D₂ ≤ M ∧ M ≤ d.N₂ ∧ d.N₂ = M ⊔ conjR M d.t ∧
    ⁅M, conjR M d.t⁆ ≤ d.D₂ ∧ d.D₂.relIndex (M ⊓ conjR M d.t) ∣ 3 ∧
    ∃ _ : (d.D₂.subgroupOf M).Normal, ∃ ψ : SL(3, F) →* M ⧸ d.D₂.subgroupOf M,
      Function.Surjective ψ ∧ ψ.ker ≤ center SL(3, F)
  P_le₁ : d.P ≤ d.N₁
  P_le₂ : d.P ≤ d.N₂
  sylow_P₁ : IsSylowOf 2 d.P d.N₁
  sylow_P₂ : IsSylowOf 2 d.P d.N₂
  card_P : Nat.card d.P = 2 ^ 30
  P_H : d.P ⊓ d.H = d.S
  D₁_le_P : d.D₁ ≤ d.P
  D₂_le_P : d.D₂ ≤ d.P
  V₁_center : d.V₁ ≤ centralizer (d.P : Set G)
  card_P_w₁ : Nat.card (d.P ⊓ conjR d.P d.w₁ : Subgroup G) = 2 ^ 26
  card_P_w₂ : Nat.card (d.P ⊓ conjR d.P d.w₂ : Subgroup G) = 2 ^ 26
  card_P_w₃ : Nat.card (d.P ⊓ conjR d.P d.w₃ : Subgroup G) = 2 ^ 28
  N₁_gen : d.N₁ = d.P ⊔ zpowers d.w₂ ⊔ zpowers d.w₃
  N₂_gen : d.N₂ = d.P ⊔ zpowers d.w₁ ⊔ zpowers d.w₂

end CFSG.EvenSmallLie.UnitarySix.YamadaEnd
