module

public import CFSG.GH74.GLS.Stage4.RestOut

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def Ch6Notation.u (D : Ch6Notation G) : G := D.a⁻¹ * D.z * D.a

@[expose] def Ch6Notation.A (D : Ch6Notation G) (b : Bool) : Subgroup G := if b then D.X₁' else D.X₁

@[expose] def Ch6Notation.B (D : Ch6Notation G) (b : Bool) : Subgroup G := if b then D.X₂' else D.X₂

@[expose] def Ch6Notation.Shape (D : Ch6Notation G) (α β γ δ : Bool) : Prop :=
  (D.P : Set G) = (D.X₁ : Set G) * (D.X₂ : Set G) * (conjBy D.a (D.A α) : Set G) *
    (conjBy D.a (D.B β) : Set G) * (conjBy (D.a ^ 2) (D.A γ) : Set G) *
    (conjBy (D.a ^ 2) (D.B δ) : Set G)

@[expose] def Ch6Notation.Rfac (D : Ch6Notation G) (α β γ δ : Bool) : Set (Subgroup G) :=
  {conjBy D.a (D.A α), conjBy D.a (D.B β), conjBy (D.a ^ 2) (D.A γ), conjBy (D.a ^ 2) (D.B δ)}

structure Ch6PreP (D : Ch6Notation G) : Prop where
  K_inter : D.K₁ ⊓ D.K₂ ≤ Subgroup.zpowers D.z
  u_inv_X₁ : ∀ x ∈ D.X₁, D.u * x * D.u⁻¹ = x⁻¹
  u_inv_X₁' : ∀ x ∈ D.X₁', D.u * x * D.u⁻¹ = x⁻¹
  u_inv_X₂ : ∀ x ∈ D.X₂, D.u * x * D.u⁻¹ = x⁻¹
  u_inv_X₂' : ∀ x ∈ D.X₂', D.u * x * D.u⁻¹ = x⁻¹
  a_cycle : D.a⁻¹ * D.u * D.a = D.z * D.u
  P_pGroup : IsPGroup D.p ↥D.P
  P_card : Nat.card ↥D.P = D.q₁ ^ 3 * D.q₂ ^ 3
  P_normH : ∀ h ∈ D.H, ∀ x ∈ D.P, h * x * h⁻¹ ∈ D.P
  X₂_central : ∀ x ∈ D.X₂, ∀ y ∈ D.P, x * y = y * x
  shape : ∃ α β γ δ : Bool, D.Shape α β γ δ ∧
    centralizer ({D.z} : Set G) ⊓ D.P = D.X₁ ⊔ D.X₂ ∧
    centralizer ({D.u} : Set G) ⊓ D.P = conjBy D.a (D.A α ⊔ D.B β) ∧
    centralizer ({D.z * D.u} : Set G) ⊓ D.P = conjBy (D.a ^ 2) (D.A γ ⊔ D.B δ)
  inequiv : ∀ i j : ℤ, IsRoot 6 i → IsRoot 6 j → D.root i ≤ D.P → D.root j ≤ D.P → i ≠ j →
    ¬ HEquiv D.H (D.root i) (D.root j)
  comm_R : ∀ α β γ δ : Bool, D.Shape α β γ δ → ∀ S₁ ∈ D.Rfac α β γ δ, ∀ S₂ ∈ D.Rfac α β γ δ,
    ∀ x ∈ S₁, ∀ y ∈ S₂, ⁅x, y⁆ ∈ D.X₂
  F_normB : D.F ≤ normalizer ((D.H ⊔ D.P : Subgroup G) : Set G)
  P₀_normP : D.P₀ ≤ normalizer (D.P : Set G)
  Sylow_PP₀ : ∃ T : Sylow D.p G, (T : Subgroup G) = D.P ⊔ D.P₀

structure Ch6Pre (D : Ch6Notation G) : Prop where
  basics : Ch6Basics D
  pre : Ch6PreP D

end CFSG.GH74.GLS.Stage4.Rest
