module

public import CFSG.GH74.GLS.SP.Local.SPLStages

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Defs

variable {G : Type} [Group G] (D : SPLNot3 G)

@[expose] def SPLNot3.C₂ : Subgroup G := centralizer (D.X₂ : Set G)

@[expose] def SPLNot3.V₂ : Subgroup G := pPrimeCoreOf 2 D.C₂

@[expose] def L34Concl : Prop :=
  ∃ V : Subgroup G, V ≤ centralizer (D.Y₁ : Set G) ∧
    (V.subgroupOf (centralizer (D.Y₁ : Set G))).Normal ∧ Odd (Nat.card ↥V) ∧
    (∃ k : ℕ, Nat.card ↥(centralizer (D.Y₁ : Set G)) = 2 ^ k * Nat.card ↥V) ∧
    ⁅V, zpowers (D.z * D.t)⁆ = D.Y₁

end Defs

@[expose] def SPLInL33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot3 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D.toSPLNot2 → SPL2Ord D.toSPLNot0 →
      SPL3X D → SPL3Aa D → ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x

@[expose] def SPLInL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot3 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D.toSPLNot2 → SPL2Ord D.toSPLNot0 →
      SPL3X D → SPL3Aa D → L34Concl D

@[expose] def SPLInC2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ D : SPLNot3 G,
    SPLSetup D.toSPLNot0 → SPL2Set D.toSPLNot1 → SPL2Ct D.toSPLNot2 → SPL3X D →
      D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁

structure R2A {G : Type} [Group G] (D : SPLNot3 G) : Prop where
  z_mem_C₂ : D.z ∈ D.C₂
  K₁_le_C₂ : D.K₁ ≤ D.C₂
  X₂_le_V₂ : D.X₂ ≤ D.V₂
  V₂_odd : Odd (Nat.card ↥D.V₂)
  V₂_norm : ∀ g ∈ D.C₂, ∀ v ∈ D.V₂, g * v * g⁻¹ ∈ D.V₂
  V₂_cen_z : ∀ v ∈ D.V₂, D.z * v * D.z⁻¹ = v → v ∈ D.X₂
  z_cen_mod : ∀ g ∈ D.C₂, ⁅g, D.z⁆ ∈ D.V₂
  z_inv_mod : ∀ v ∈ D.V₂, D.z * v * D.z⁻¹ * v ∈ D.X₂
  V₂_class2 : ∀ u ∈ D.V₂, ∀ v ∈ D.V₂, ⁅u, v⁆ ∈ D.X₂

structure R2B {G : Type} [Group G] (D : SPLNot3 G) : Prop where
  X₃_le_V₂ : D.X₃ ≤ D.V₂
  X₄_le_V₂ : D.X₄ ≤ D.V₂
  V₂_pgroup : IsPGroup D.p ↥D.V₂

end CFSG.GH74.GLS.SP.Local
