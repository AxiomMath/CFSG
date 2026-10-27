module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactOm6Par : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) (K₁ K₂ : Subgroup G),
    IsOm6Z2 L → oddCoreIn L = ⊥ → orderOf z = 2 → Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ →
      K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ → K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) →
        ∀ g y : G, g ∈ normalizer (L : Set G) → CFSG.conjugate K₁ g = K₁ →
          CFSG.conjugate K₂ g = K₂ → y ∈ normalizer (L : Set G) →
          K₁ ⊔ K₂ ≤ centralizer ({y} : Set G) → y * y ∈ centralizer (L : Set G) →
          y ∉ centralizer (L : Set G) → y * z ∉ centralizer (L : Set G) →
            (Xor' (∃ k ∈ K₁, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn K₁)
                (∃ k ∈ K₂, g⁻¹ * k * g * k⁻¹ ∉ twoCoreIn K₂) ↔
              (y⁻¹ * (g⁻¹ * y * g) ∉ centralizer (L : Set G) ∧
                (y * z)⁻¹ * (g⁻¹ * y * g) ∉ centralizer (L : Set G)))

end CFSG.OddStandard.SmallF3.Omega
