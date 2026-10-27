module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.GH74.GLS.Stage1.Thm6

open Subgroup

variable {G : Type*} [Group G]

@[expose] def IsSylow2In (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup 2 ↥P ∧ ¬ 2 ∣ P.relIndex H

end CFSG.GH74.GLS.Stage1.Thm6
