module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

@[expose] def OddFixFourth (Y : Type*) [Group Y] : Prop :=
  ∀ z : Y, orderOf z = 2 → ∀ φ : MulAut Y,
    (∀ x ∈ centralizer ({z} : Set Y), Odd (orderOf x) → φ x = x) → φ ^ 4 = 1

end CFSG.EvenSporadicStandard.TwoHS
