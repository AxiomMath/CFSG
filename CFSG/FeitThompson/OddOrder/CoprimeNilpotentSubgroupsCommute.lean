module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Local.CentralCommutatorPowers

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped commutatorElement

variable {X : Type*} [Group X]

theorem commute_of_coprime_orderOf (X : Type*) [Group X] [Group.IsNilpotent X] (x y : X)
    (h : (orderOf x).Coprime (orderOf y)) : Commute x y := by
  revert x y
  refine Group.nilpotent_center_quotient_ind X
    (P := fun X _ _ => ∀ x y : X, (orderOf x).Coprime (orderOf y) → Commute x y) ?_ ?_
  · intro X _ _ x y _
    exact Subsingleton.elim x y ▸ rfl
  · intro X _ _ ih x y h
    have hq : ⁅x, y⁆ ∈ Subgroup.center X := by
      have hcom := ih (QuotientGroup.mk' (Subgroup.center X) x)
        (QuotientGroup.mk' (Subgroup.center X) y)
        ((h.coprime_dvd_left (orderOf_map_dvd _ x)).coprime_dvd_right (orderOf_map_dvd _ y))
      have hone : (QuotientGroup.mk' (Subgroup.center X)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]; exact hcom
      simpa using (QuotientGroup.eq_one_iff _).mp hone
    have hx : orderOf ⁅x, y⁆ ∣ orderOf x :=
      orderOf_dvd_of_pow_eq_one (by
        rw [← commutatorElement_pow_left_of_mem_center hq, pow_orderOf_eq_one,
          commutatorElement_one_left])
    have hy : orderOf ⁅x, y⁆ ∣ orderOf y :=
      orderOf_dvd_of_pow_eq_one (by
        rw [← commutatorElement_pow_right_of_mem_center hq, pow_orderOf_eq_one,
          commutatorElement_one_right])
    rw [← commutatorElement_eq_one_iff_commute, ← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes h hx hy

variable {R S : Subgroup X}

theorem commute_of_coprime_natCard [Group.IsNilpotent X]
    (h : (Nat.card R).Coprime (Nat.card S)) {r s : X} (hr : r ∈ R) (hs : s ∈ S) :
    Commute r s :=
  commute_of_coprime_orderOf X r s
    ((h.coprime_dvd_left (R.orderOf_dvd_natCard hr)).coprime_dvd_right
      (S.orderOf_dvd_natCard hs))

theorem commutator_eq_bot_of_coprime_natCard [Group.IsNilpotent X]
    (h : (Nat.card R).Coprime (Nat.card S)) : ⁅R, S⁆ = ⊥ :=
  eq_bot_iff.mpr <| Subgroup.commutator_le.mpr fun _ hr _ hs =>
    Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_commute.mpr
      (commute_of_coprime_natCard h hr hs))

theorem le_centralizer_of_coprime_natCard [Group.IsNilpotent X]
    (h : (Nat.card R).Coprime (Nat.card S)) : R ≤ Subgroup.centralizer (S : Set X) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_coprime_natCard h)

end

end CFSG.FeitThompson
