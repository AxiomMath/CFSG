module

public import Mathlib.GroupTheory.IsPerfect

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Group Subgroup

variable (G : Type*) [Group G]

theorem derivedSeries_eq_top_of_commutator_eq_top (h : _root_.commutator G = ⊤) (n : ℕ) :
    derivedSeries G n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def, h]

theorem subsingleton_of_isSolvable_of_commutator_eq_top [Group.IsSolvable G]
    (h : _root_.commutator G = ⊤) : Subsingleton G := by
  rw [← not_nontrivial_iff_subsingleton]
  intro _
  have : Group.IsPerfect G := Group.isPerfect_def.mpr h
  exact Group.IsPerfect.not_isSolvable G ‹Group.IsSolvable G›

theorem top_eq_bot_of_isSolvable_of_commutator_eq_top [Group.IsSolvable G]
    (h : _root_.commutator G = ⊤) : (⊤ : Subgroup G) = ⊥ := by
  have := subsingleton_of_isSolvable_of_commutator_eq_top G h
  exact Subsingleton.elim _ _

end CFSG.FeitThompson
