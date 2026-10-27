module
public import Mathlib.GroupTheory.IsPerfect
import CFSG.FeitThompson.Foundations.DerivedSubgroupCharacteristic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem commutator_eq_top_of_not_isMulCommutative [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    _root_.commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator G) with hb | ht
  · exact absurd ((_root_.commutator_eq_bot_iff G).mp hb) h
  · exact ht

theorem isPerfect_of_not_isMulCommutative [IsSimpleGroup G] (h : ¬ IsMulCommutative G) :
    Group.IsPerfect G :=
  Group.isPerfect_def.mpr (commutator_eq_top_of_not_isMulCommutative h)

theorem closure_setOf_inv_mul_inv_mul_mul_eq_top_of_not_isMulCommutative [IsSimpleGroup G]
    (h : ¬ IsMulCommutative G) :
    Subgroup.closure {g : G | ∃ x y : G, x⁻¹ * y⁻¹ * x * y = g} = ⊤ := by
  rw [closure_setOf_inv_mul_inv_mul_mul_eq_commutator]
  exact commutator_eq_top_of_not_isMulCommutative h

theorem commutator_eq_top_of_oddOrder_of_proper_solvable [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) :
    _root_.commutator G = ⊤ :=
  commutator_eq_top_of_not_isMulCommutative hna

end CFSG.FeitThompson
