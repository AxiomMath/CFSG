module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.HardMathSupport.Malle.Proving

theorem not_dvd_of_dvd_sq_add_add_one {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ 2 + q + 1) :
    ¬ p ∣ q := by
  intro hq
  have h1 : p ∣ q ^ 2 + q := dvd_add (dvd_pow hq two_ne_zero) hq
  exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h))

theorem sq_sub_add_one_zmod_eq_zero {p q : ℕ} (h : p ∣ q ^ 2 - q + 1) :
    ((q : ℕ) : ZMod p) ^ 2 - ((q : ℕ) : ZMod p) + 1 = 0 := by
  have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have := (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).2 h
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hle, Nat.cast_pow] at this
  exact this

theorem not_dvd_of_dvd_sq_sub_add_one {p q : ℕ} (hp : p.Prime) (h : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q := by
  intro hq
  have : Fact p.Prime := ⟨hp⟩
  have hx := sq_sub_add_one_zmod_eq_zero h
  have hq0 : ((q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).2 hq
  rw [hq0] at hx
  norm_num at hx

theorem ne_two_of_dvd_sq_sub_add_one {p q : ℕ} (h : p ∣ q ^ 2 - q + 1) : p ≠ 2 := by
  rintro rfl
  have hx := sq_sub_add_one_zmod_eq_zero h
  revert hx
  generalize ((q : ℕ) : ZMod 2) = y
  revert y
  decide

theorem not_int_dvd_sub_one_sq_of_orderOf {p q e : ℕ} (hp : p.Prime)
    (he : orderOf ((q : ℕ) : ZMod p) = e) (he1 : e ≠ 1) :
    ¬ (p : ℤ) ∣ ((q : ℤ) - 1) * ((q : ℤ) - 1) := by
  intro hd
  have : Fact p.Prime := ⟨hp⟩
  have h0 : ((((q : ℤ) - 1) * ((q : ℤ) - 1) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hd
  push_cast at h0
  have h1 : ((q : ℕ) : ZMod p) - 1 = 0 := mul_self_eq_zero.1 h0
  have h2 : ((q : ℕ) : ZMod p) = 1 := sub_eq_zero.1 h1
  rw [h2, orderOf_one] at he
  exact he1 he.symm

end CFSG.HardMathSupport.Malle.Proving
