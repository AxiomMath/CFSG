module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactOm6CentD : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) (K₁ K₂ : Subgroup G),
    IsOm6Z2 L → oddCoreIn L = ⊥ → orderOf z = 2 → Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ →
      K₁ ≠ K₂ → ⁅K₁, K₂⁆ = ⊥ → K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) →
        ∀ Y : Subgroup G,
          Y ≤ normalizer (L : Set G) ⊓ centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) →
            (centralizer (L : Set G)).relIndex Y ∣ 8

end CFSG.OddStandard.SmallF3.Omega
