module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

@[expose] def Asc82Fact512M8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
    ∀ t : G, orderOf t = 2 → centerIn L = zpowers t →
      ∀ r : G, orderOf r = 2 → (∃ α : ℤˣ, InducesTypeSome L r 6 (-1) 1 α) →
        ∀ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) → IsElemAb2 B 5 → t ∈ B →
          zpowers t ⊓ layerCent L r = ⊥ → B = zpowers t ⊔ (B ⊓ layerCent L r) →
          ∀ z : G, IsI4PlusIn L z → z ∈ zpowers r ⊔ B →
            8 ≤ Nat.card ↥((zpowers r ⊔ B) ⊓ twoRes (L ⊓ centralizer ({z} : Set G)))

end CFSG.OddStandard.SmallF3.Omega
