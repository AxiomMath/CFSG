module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Sec5FactB5z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, t ∈ centerIn L → orderOf t = 2 →
      ∀ z : G, IsI4PlusIn L z →
        ∀ r : G, orderOf r = 2 → r * z = z * r →
          (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
            ∃ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) ∧ IsElemAb2 B 5 ∧ t ∈ B ∧ z ∈ B ∧
              zpowers t ⊓ layerCent L r = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L r)

end CFSG.OddStandard.SmallF3.Omega
