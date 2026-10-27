module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G] {x l : G}

theorem commute_of_commute_commutatorElement (hxa : Commute x ⁅x, l⁆)
    (hcop : (orderOf x).Coprime (orderOf ⁅x, l⁆)) : Commute x l := by
  set a : G := ⁅x, l⁆ with ha_def
  have hxl : x * l * x⁻¹ = a * l := by
    rw [ha_def, commutatorElement_def]
    group
  have key : ∀ j : ℕ, x ^ j * l * (x ^ j)⁻¹ = a ^ j * l := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc x ^ (j + 1) * l * (x ^ (j + 1))⁻¹ = x ^ j * (x * l * x⁻¹) * (x ^ j)⁻¹ := by group
        _ = x ^ j * a * l * (x ^ j)⁻¹ := by rw [hxl]; group
        _ = a * (x ^ j * l * (x ^ j)⁻¹) := by rw [(hxa.pow_left j).eq]; group
        _ = a ^ (j + 1) * l := by rw [ih, pow_succ', mul_assoc]
  have hak : a ^ orderOf x = 1 := by
    have h := key (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, right_eq_mul] at h
    exact h
  have ha1 : orderOf a = 1 := hcop.symm.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hak)
  exact commutatorElement_eq_one_iff_commute.mp (orderOf_eq_one_iff.mp ha1)

theorem commute_of_commute_commutatorElement_of_odd (hxa : Commute x ⁅x, l⁆)
    (ha2 : ⁅x, l⁆ * ⁅x, l⁆ = 1) (hodd : Odd (orderOf x)) : Commute x l := by
  refine commute_of_commute_commutatorElement hxa ?_
  have h2 : orderOf ⁅x, l⁆ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, ha2])
  exact (Nat.coprime_two_right.mpr hodd).coprime_dvd_right h2

end CFSG.GroupTheory
