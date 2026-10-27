module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Equiv
public import CFSG.GH74.GLS.Balance.Defs

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4
open scoped commutatorElement

@[expose] def DiagLayerS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ K : Subgroup G, IsRigidRankOneComp a K → b ∉ normalizer (K : Set G) →
      ∃ Λ : Subgroup G,
        Λ = pLayerOf 2 ((K ⊔ cmap b K) ⊓ centralizer ({b} : Set G)) ∧
        IsPCompIn 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) Λ ∧
        Λ ≤ (K ⊔ cmap b K) ⊓ centralizer ({b} : Set G) ∧
        (∀ k ∈ K, ∃ l ∈ Λ, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)), l = k * (b * k * b⁻¹) * o) ∧
        (∀ l ∈ Λ, ∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)), l = k * (b * k * b⁻¹) * o) ∧
        ∀ g ∈ (K ⊔ cmap b K) ⊓ centralizer ({b} : Set G), (∃ n : ℕ, g ^ (2 ^ n) = 1) →
          (∃ k ∈ K, ∃ o ∈ pPrimeCoreOf 2 (centralizer ({a} : Set G)), g = k * (b * k * b⁻¹) * o) → g ∈ Λ

@[expose] def BLS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ Λ : Subgroup G,
      IsPCompIn 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) Λ → pRank 2 ↥Λ = 1 →
        ∀ y ∈ Λ, orderOf y = 2 → ∀ L : Subgroup G, IsRigidRankOneComp b L → y ∈ cSec L

@[expose] def BL0S : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ H : Subgroup G,
      H ≤ pLayerOf 2 (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) →
        ∀ y : G, y ∈ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) → y ∈ zStar (rigidProduct b) →
          ∀ l ∈ H, ⁅l, y⁆ ∈ pPrimeCoreOf 2 (centralizer ({b} : Set G))

@[expose] def BL0sS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ V : Subgroup G,
      Balance.IsSolvTwoCompSL23In (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)) V →
        ∀ y : G, y ∈ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) → y ∈ zStar (rigidProduct b) →
          ∀ v ∈ oPrimeResidualOf 2 V, ⁅v, y⁆ ∈ pPrimeCoreOf 2 (centralizer ({b} : Set G))

@[expose] def Bal1S : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ K : Subgroup G, IsRigidRankOneComp a K →
      b ∈ normalizer (K : Set G) → InducesFAut b K →
        ∃ y ∈ K, orderOf y = 2 ∧ y ∈ centralizer ({b} : Set G) ∧
          ∀ L : Subgroup G, IsRigidRankOneComp b L → y ∈ cSec L

@[expose] def BalSwapS : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsKProperSimple G → ∀ (a b : G), orderOf a = 2 → orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) → ∀ K₁ K₂ : Subgroup G, IsRigidRankOneComp a K₁ → IsRigidRankOneComp a K₂ →
      K₁ ≠ K₂ → cmap b K₁ = K₂ → ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({a} : Set G)) →
        b ∈ T → ∀ z₁ z₂ : G, z₁ ∈ T ⊓ K₁ → z₂ ∈ T ⊓ K₂ → orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
          ∀ L : Subgroup G, IsRigidRankOneComp b L → z₁ * z₂ ∈ cSec L

end CFSG.GH74.GLS.Bg.Pu5
