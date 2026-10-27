module

public import CFSG.GH74.GLS.Stage4.T2Defs
public import CFSG.GH74.GLS.IVK.Defs2
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.Assembly.LowTwoRank

section Four1

variable {G : Type} [Group G]

structure T2Four1 (C₁ : Subgroup G) (z u : G) (K₁ K₂ H : Subgroup G) (w₁ w₂ : G) : Prop where
  zz : z * z = 1
  z_ne : z ≠ 1
  uu : u * u = 1
  u_ne : u ≠ 1
  zu_ne : z ≠ u
  zu_comm : z * u = u * z
  K_comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  K_inter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z
  C_comm : ∀ x ∈ C₁, x * z = z * x
  K_le_C : K₁ ⊔ K₂ ≤ C₁
  C_norm₁ : ∀ c ∈ C₁, ∀ x ∈ K₁, c * x * c⁻¹ ∈ K₁
  C_norm₂ : ∀ c ∈ C₁, ∀ x ∈ K₂, c * x * c⁻¹ ∈ K₂
  C_idx : (K₁ ⊔ K₂).relIndex C₁ = 2
  H_comm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x
  z_mem_H : z ∈ H
  u_mem_H : u ∈ H
  H_le_C : H ≤ C₁
  H_not_le_K : ¬ H ≤ K₁ ⊔ K₂
  H₁_iff : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x
  H₂_iff : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x
  w₁_mem : w₁ ∈ K₁
  w₂_mem : w₂ ∈ K₂
  w₁_sq : w₁ * w₁ = z
  w₂_sq : w₂ * w₂ = z
  w₁_u : w₁ * u * w₁⁻¹ = u * z
  w₂_u : w₂ * u * w₂⁻¹ = u * z
  w₁_normH : ∀ h ∈ H, w₁ * h * w₁⁻¹ ∈ H
  w₂_normH : ∀ h ∈ H, w₂ * h * w₂⁻¹ ∈ H
  w₀_inv : ∀ h ∈ H, (w₁ * w₂) * h * (w₁ * w₂)⁻¹ = h⁻¹
  w₀_not_mem : w₁ * w₂ ∉ H

structure Ch6NegCfg (C₁ : Subgroup G) (q : ℕ) (z u : G) (K₁ K₂ H : Subgroup G) (w₁ w₂ : G) : Prop
    extends T2Four1 C₁ z u K₁ K₂ H w₁ w₂ where
  H₁_cyc : IsCyclic ↥(H ⊓ K₁)
  H₂_cyc : IsCyclic ↥(H ⊓ K₂)
  H₁_card : Nat.card ↥(H ⊓ K₁) = q + 1
  H₂_card : Nat.card ↥(H ⊓ K₂) = q + 1
  H_idx : ((H ⊓ K₁) ⊔ (H ⊓ K₂)).relIndex H = 2
  H₁_cent : ∀ y ∈ H ⊓ K₁, y * y ≠ 1 → ∀ d ∈ K₁, d * y = y * d → d ∈ H
  H₂_cent : ∀ y ∈ H ⊓ K₂, y * y ≠ 1 → ∀ d ∈ K₂, d * y = y * d → d ∈ H

end Four1

@[expose] def Ch6T2NegCfgMod (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Gs : Type) [Group Gs] (q : ℕ) (z : G) (K₁ K₂ : Subgroup G)
    (F₁ F₂ : Type) [Field F₁] [Field F₂] (t : G),
    Ch6Setup G Gs q q z K₁ K₂ F₁ F₂ → Ch6Rem z K₁ K₂ F₁ F₂ t → q % 4 = r →
      ∃ (u : G) (H : Subgroup G) (w₁ w₂ : G),
        Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z u K₁ K₂ H w₁ w₂

end CFSG.GH74.GLS.Stage4.Rest

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def IVK_4_1_R_U3 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (p n : ℕ), p.Prime → p ≠ 2 →
    (IsSLnEps 3 J (-1) (p ^ n) ∨ IsLnEps 3 J (-1) (p ^ n)) →
      ∀ z : J, orderOf z = 2 → ∀ X : Subgroup J, X ≤ centralizer ({z} : Set J) → IsPGroup p ↥X →
        Nat.card ↥X = p ^ n →
          ∃ R : Subgroup J, R = CFSG.Open.pCoreOf p (centralizer (X : Set J)) ∧ IsPGroup p ↥R ∧ X ≤ R ∧
            R ≤ centralizer (X : Set J) ∧ Nat.card ↥R = (p ^ n) ^ 3 ∧
            (∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ∈ X) ∧ X ≤ ⁅R, R⁆ ∧ (∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) ∧
            (∀ r ∈ R, z * r * z⁻¹ * r ∈ X)

end CFSG.GH74.GLS.IVK
