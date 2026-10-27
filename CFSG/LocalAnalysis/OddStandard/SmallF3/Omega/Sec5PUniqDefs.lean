module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82FactPocketsUniq6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), IsOm6Z2 L → IsI4PlusIn L z →
    ∀ K₁ K₂ : Subgroup G, Sl23PocketIn L z K₁ → Sl23PocketIn L z K₂ → K₁ ≠ K₂ →
      Nonempty (↥(twoCoreIn K₁) ≃* QuaternionGroup 2) →
      Nonempty (↥(twoCoreIn K₂) ≃* QuaternionGroup 2) →
      ⁅twoCoreIn K₁, twoCoreIn K₂⁆ = ⊥ → Nat.card ↥(twoCoreIn K₁ ⊔ twoCoreIn K₂) = 32 →
      centerIn (twoCoreIn K₁ ⊔ twoCoreIn K₂) = zpowers z →
        (∀ K : Subgroup G, Sl23PocketIn L z K →
            twoCoreIn K = twoCoreIn K₁ ∨ twoCoreIn K = twoCoreIn K₂) ∧
        twoRes (L ⊓ centralizer ({z} : Set G)) ≤ oddCoreIn L ⊔ K₁ ⊔ K₂

end CFSG.OddStandard.SmallF3.Omega
