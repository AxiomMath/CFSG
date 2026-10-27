module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

@[expose] def tInvolutions {Y : Type} [Group Y] (t : Y) (τ : Y → Prop) : Set Y :=
  {y : Y | y ∈ centralizer ({t} : Set Y) ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧ τ y}

@[expose] def Wsub {Y : Type} [Group Y] (t : Y) (τ : Y → Prop) : Subgroup Y :=
  Subgroup.closure (tInvolutions t τ)

end CFSG.EvenSporadicStandard.HNRecog.Harada
