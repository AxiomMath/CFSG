module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def DeltaPrime5 (z : G) (Q : Subgroup G) (Γ : Set (Subgroup G)) : Set G :=
  {d | d = z ∨ (orderOf d = 2 ∧ d ∈ Q ∧ ∀ P ∈ Γ, ¬ P ≤ centralizer ({d} : Set G))}

@[expose] def Asc82Fact517Fuse : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z r : G)
    (B A K₁ K₂ : Subgroup G) (h : G), Sec5HCtx G t L S z r B A K₁ K₂ h →
      ∃ m ∈ normalizer (A : Set G),
        m⁻¹ * z * m ∈ DeltaPrime5 z (Qsub K₁ K₂ h) (Gamma5 K₁ K₂ h) ∧ m⁻¹ * z * m ≠ z

@[expose] def Asc82FactSwap6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) (K₁ K₂ : Subgroup G),
    IsOm6Z2 L → oddCoreIn L = ⊥ → Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ → K₁ ≠ K₂ →
      ⁅K₁, K₂⁆ = ⊥ → K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) →
        ∃ c ∈ L ⊓ centralizer ({z} : Set G), CFSG.conjugate K₁ c = K₂

end CFSG.OddStandard.SmallF3.Omega
