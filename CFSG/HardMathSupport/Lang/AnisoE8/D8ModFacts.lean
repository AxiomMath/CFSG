module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Lang.AnisoE8

theorem dvd_pow_sub_one_iff {P q : ℕ} (hP : P.Prime) (hq : 1 ≤ q)
    (he : orderOf (q : ZMod P) = 8) (n : ℕ) : P ∣ q ^ n - 1 ↔ 8 ∣ n := by
  have := Fact.mk hP
  have hqn : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hqn, Nat.cast_pow, Nat.cast_one, sub_eq_zero,
    ← he, orderOf_dvd_iff_pow_eq_one]

theorem cast_ne_zero_of_orderOf_eq_eight {P q : ℕ} (hP : P.Prime)
    (he : orderOf (q : ZMod P) = 8) : (q : ZMod P) ≠ 0 := by
  have := Fact.mk hP
  intro h
  rw [h, orderOf_zero] at he
  omega

theorem nine_le_of_orderOf_eq_eight {P q : ℕ} (hP : P.Prime) (he : orderOf (q : ZMod P) = 8) :
    9 ≤ P := by
  have := Fact.mk hP
  have h := ZMod.orderOf_dvd_card_sub_one (cast_ne_zero_of_orderOf_eq_eight hP he)
  rw [he] at h
  have := hP.two_le
  have := Nat.le_of_dvd (by omega) h
  omega

theorem not_dvd_pow_of_orderOf_eq_eight {P q : ℕ} (hP : P.Prime)
    (he : orderOf (q : ZMod P) = 8) (k : ℕ) : ¬ P ∣ q ^ k := by
  have := Fact.mk hP
  intro hd
  apply cast_ne_zero_of_orderOf_eq_eight hP he
  have h : ((q ^ k : ℕ) : ZMod P) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
  rw [Nat.cast_pow] at h
  exact pow_eq_zero_iff'.1 h |>.1

theorem not_dvd_q16 {P q : ℕ} (hP : P.Prime) (hq : 1 ≤ q) (he : orderOf (q : ZMod P) = 8) :
    ¬ P ∣ q ^ 16 + q ^ 8 + 1 := by
  intro hd
  have h8 : P ∣ q ^ 8 - 1 := (dvd_pow_sub_one_iff hP hq he 8).2 dvd_rfl
  have hq8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq
  have e : q ^ 16 + q ^ 8 + 1 = (q ^ 8 - 1) * (q ^ 8 + 2) + 3 := by
    zify [hq8]
    ring
  rw [e] at hd
  have h3 : P ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_left h8 _)).1 hd
  have := Nat.le_of_dvd (by norm_num) h3
  have := nine_le_of_orderOf_eq_eight hP he
  omega

end CFSG.HardMathSupport.Lang.AnisoE8
