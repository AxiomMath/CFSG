module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.EvenSporadicStandard

open Subgroup

@[expose] def CatNoAlmostSimpleZ2 (A : Type) [Group A] : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S : Subgroup K), S.Normal → IsSimpleGroup ↥S →
    CFSG.Blueprint.Catalog ↥S → centralizer (S : Set K) = ⊥ → ∀ z : K, orderOf z = 2 →
      ¬ Nonempty (↥(centralizer ({z} : Set K)) ≃* Multiplicative (ZMod 2) × A)

end CFSG.EvenSporadicStandard
