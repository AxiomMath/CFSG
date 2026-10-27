module

public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.Assembly.LowTwoRank
open CFSG.GH74.GLS.Stage4.Rest.T2
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure Ch6Loc5W (N : T2N1 G) (u : G) : Prop where
  q₁_odd : Odd N.q₁
  q₂_odd : Odd N.q₂
  q₂_le : N.q₂ ≤ N.q₁
  q₁_ge : 5 ≤ N.q₁
  q₂_ge : 3 ≤ N.q₂
  q₁_pp : ∃ (p m : ℕ), p.Prime ∧ N.q₁ = p ^ m
  q₂_pp : ∃ (p m : ℕ), p.Prime ∧ N.q₂ = p ^ m
  z_ord : orderOf N.z = 2
  one_class : ∀ x : G, orderOf x = 2 → IsConj N.z x
  O2prime : pPrimeCore 2 ↥(centralizer ({N.z} : Set G)) = ⊥
  K_comm : ∀ x ∈ N.K₁, ∀ y ∈ N.K₂, x * y = y * x
  iso₁ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = N.q₁ ∧ Nonempty (↥N.K₁ ≃* SL2 F)
  iso₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = N.q₂ ∧ Nonempty (↥N.K₂ ≃* SL2 F)
  z_mem_K₁ : N.z ∈ N.K₁
  z_mem_K₂ : N.z ∈ N.K₂
  K_inter : N.K₁ ⊓ N.K₂ ≤ Subgroup.zpowers N.z
  u_ord : orderOf u = 2
  u_ne : u ≠ N.z
  u_comm : u * N.z = N.z * u
  S_pGroup : IsPGroup 2 ↥N.S
  S_sylow : ¬ 2 ∣ N.S.index
  z_mem_S : N.z ∈ N.S
  z_cent_S : ∀ s ∈ N.S, s * N.z = N.z * s
  u_mem_S : u ∈ N.S
  S_idx : (N.S ⊓ (N.K₁ ⊔ N.K₂)).relIndex N.S = 2
  w₁_memS : N.w₁ ∈ N.S
  w₂_memS : N.w₂ ∈ N.S
  K₁_eq : N.K₁ = N.X₁ ⊔ N.X₁'
  K₂_eq : N.K₂ = N.X₂ ⊔ N.X₂'
  card_X₂ : Nat.card ↥N.X₂ = N.q₂
  card_X₂' : Nat.card ↥N.X₂' = N.q₂
  X₂_comm : ∀ x ∈ N.X₂, ∀ y ∈ N.X₂, x * y = y * x
  X₂'_comm : ∀ x ∈ N.X₂', ∀ y ∈ N.X₂', x * y = y * x
  X₁_exp : ∀ x ∈ N.X₁, x ^ N.q₁.minFac = 1
  X₁'_exp : ∀ x ∈ N.X₁', x ^ N.q₁.minFac = 1
  X₂_exp : ∀ x ∈ N.X₂, x ^ N.q₂.minFac = 1
  X₂'_exp : ∀ x ∈ N.X₂', x ^ N.q₂.minFac = 1
  X₂_ne : N.X₂ ≠ N.X₂'
  H_comm : ∀ x ∈ N.H, ∀ y ∈ N.H, x * y = y * x
  z_mem_H : N.z ∈ N.H
  u_mem_H : u ∈ N.H
  H₁_eq : N.H ⊓ N.K₁ = centralizer ({u} : Set G) ⊓ N.K₁
  H₂_eq : N.H ⊓ N.K₂ = centralizer ({u} : Set G) ⊓ N.K₂
  H₁_cyc : IsCyclic ↥(N.H ⊓ N.K₁)
  H₂_cyc : IsCyclic ↥(N.H ⊓ N.K₂)
  card_H_K₂ : Nat.card ↥(N.H ⊓ N.K₂) = N.q₂ - 1
  H_idx : ((N.H ⊓ N.K₁) ⊔ (N.H ⊓ N.K₂)).relIndex N.H = 2
  H_le : N.H ≤ N.K₁ ⊔ N.K₂ ⊔ N.S
  H_not_le_K : ¬ N.H ≤ N.K₁ ⊔ N.K₂
  H_norm_X₂ : ∀ h ∈ N.H, ∀ x ∈ N.X₂, h * x * h⁻¹ ∈ N.X₂
  H_norm_X₂' : ∀ h ∈ N.H, ∀ x ∈ N.X₂', h * x * h⁻¹ ∈ N.X₂'
  H_fpf₂ : ∀ h ∈ N.H ⊓ N.K₂, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₂, h * x * h⁻¹ = x → x = 1
  H_fpf₂' : ∀ h ∈ N.H ⊓ N.K₂, h ∉ Subgroup.zpowers N.z → ∀ x ∈ N.X₂', h * x * h⁻¹ = x → x = 1
  w₁_mem : N.w₁ ∈ N.K₁
  w₂_mem : N.w₂ ∈ N.K₂
  w₁_sq : N.w₁ * N.w₁ = N.z
  w₂_sq : N.w₂ * N.w₂ = N.z
  w₂_swap : ∀ x ∈ N.X₂, N.w₂ * x * N.w₂⁻¹ ∈ N.X₂'
  w₂_swap' : ∀ x ∈ N.X₂', N.w₂ * x * N.w₂⁻¹ ∈ N.X₂
  w₁_inv : ∀ h ∈ N.H ⊓ N.K₁, N.w₁ * h * N.w₁⁻¹ = h⁻¹
  w₂_inv : ∀ h ∈ N.H ⊓ N.K₂, N.w₂ * h * N.w₂⁻¹ = h⁻¹
  w₁_u : N.w₁ * u * N.w₁⁻¹ = u * N.z
  w₂_u : N.w₂ * u * N.w₂⁻¹ = u * N.z
  w₁_normH : N.w₁ ∈ normalizer (N.H : Set G)
  w₂_normH : N.w₂ ∈ normalizer (N.H : Set G)
  w₀_inv : ∀ h ∈ N.H, (N.w₁ * N.w₂) * h * (N.w₁ * N.w₂)⁻¹ = h⁻¹
  w₀_cent : (N.w₁ * N.w₂) * u = u * (N.w₁ * N.w₂)
  u_inv_X₂ : ∀ x ∈ N.X₂, u * x * u⁻¹ = x⁻¹
  u_inv_X₂' : ∀ x ∈ N.X₂', u * x * u⁻¹ = x⁻¹

structure Ch6Loc5M (N : T2N1 G) (u : G) : Prop extends Ch6Loc5W N u where
  card_H_K₁ : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ + 1
  H₁_cent : ∀ y ∈ N.H ⊓ N.K₁, y * y ≠ 1 → ∀ d ∈ N.K₁, d * y = y * d → d ∈ N.H

structure Ch6F5W (N : T2N2 G) : Prop where
  F_def : N.F = (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map (centralizer (N.S : Set G)).subtype
  F_odd : ∀ f ∈ N.F, Odd (orderOf f)
  F_comm : ∀ x ∈ N.F, ∀ y ∈ N.F, x * y = y * x
  F_inter_K : N.F ⊓ (N.K₁ ⊔ N.K₂) = ⊥
  C_le : centralizer ({N.z} : Set G) ≤ N.K₁ ⊔ N.K₂ ⊔ N.S ⊔ N.F
  centS : centralizer (N.S : Set G) = Subgroup.zpowers N.z ⊔ N.F
  F_normH : N.F ≤ normalizer (N.H : Set G)
  F_normX₂ : ∀ f ∈ N.F, ∀ x ∈ N.X₂, f * x * f⁻¹ ∈ N.X₂
  F_normX₂' : ∀ f ∈ N.F, ∀ x ∈ N.X₂', f * x * f⁻¹ ∈ N.X₂'

structure Ch6Sec5W (N : T2N3 G) (u : G) : Prop where
  loc : Ch6Loc5W N.toT2N2.toT2N1 u
  F5 : Ch6F5W N.toT2N2
  weyl : Ch6Weyl N
  u_eq : N.u = u

structure Ch6Sec5M (N : T2N3 G) (u : G) : Prop where
  loc : Ch6Loc5M N.toT2N2.toT2N1 u
  F5 : Ch6F5W N.toT2N2
  weyl : Ch6Weyl N
  u_eq : N.u = u

theorem Ch6Sec5M.toW {N : T2N3 G} {u : G} (h : Ch6Sec5M N u) : Ch6Sec5W N u :=
  ⟨h.loc.toCh6Loc5W, h.F5, h.weyl, h.u_eq⟩

structure Ch6Coord2 (N : T2N1 G) : Prop where
  coord₂ : ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL2 F →* G), Nat.card F = N.q₂ ∧
    Function.Injective φ ∧ φ.range = N.K₂ ∧ φ (negOne F) = N.z ∧
    N.X₂ = (uSub F).map φ ∧ N.X₂' = (lSub F).map φ ∧ N.w₂ = φ (sl2W F) ∧
    N.H ⊓ N.K₂ = (tSub F).map φ

end CFSG.GH74.GLS.Stage4.Rest
