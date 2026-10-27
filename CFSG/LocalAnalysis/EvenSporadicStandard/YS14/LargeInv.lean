module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSporadicStandard.YS14

@[expose] def IsLargeInv {T : Type*} [Group T] (x : T) : Prop :=
  x * x = 1 ∧ x ≠ 1 ∧ 2 ^ 15 ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set T))

end CFSG.EvenSporadicStandard.YS14
