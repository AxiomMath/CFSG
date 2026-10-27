module
public import Mathlib.GroupTheory.Frattini

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {X : Type*} [Group X]

theorem frattini_eq_bot_of_subsingleton [Subsingleton X] : frattini X = ⊥ :=
  Subsingleton.elim _ _

theorem eq_top_of_mul_frattini_eq_univ [Finite X] {Y : Subgroup X}
    (h : (Y : Set X) * (frattini X : Set X) = Set.univ) : Y = ⊤ := by
  refine frattini_nongenerating (K := Y) ?_
  apply SetLike.coe_injective
  rw [Subgroup.mul_normal Y (frattini X), h]
  simp

end CFSG.FeitThompson
