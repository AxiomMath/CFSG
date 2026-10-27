module

public import Mathlib.Data.Int.ModEq
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

theorem add_one_le_of_one_lt_of_modEq_one {m u : ℤ} (hu : 1 < u) (hmod : u ≡ 1 [ZMOD m]) :
    m + 1 ≤ u := by
  have hdvd : m ∣ u - 1 := hmod.symm.dvd
  have := Int.le_of_dvd (by omega : (0:ℤ) < u - 1) hdvd
  omega

theorem modEq_one_of_mul_modEq_one {m u x : ℤ} (hu : u ≡ 1 [ZMOD m])
    (hux : u * x ≡ 1 [ZMOD m]) : x ≡ 1 [ZMOD m] := by
  have h1 : m ∣ u * x - 1 := hux.symm.dvd
  have h2 : m ∣ u - 1 := hu.symm.dvd
  have h3 : m ∣ x - 1 := by
    have h4 := Int.dvd_sub h1 (Dvd.dvd.mul_right h2 x)
    have e : u * x - 1 - (u - 1) * x = x - 1 := by ring
    rwa [e] at h4
  exact ((Int.modEq_iff_dvd.2 h3 : (1:ℤ) ≡ x [ZMOD m])).symm

section CongruentProduct

variable {m u x h : ℤ} (hm : 2 ≤ m) (hu : 1 < u) (hx : 1 < x) (hh : h = u * x)
  (hhm : h ≡ 1 [ZMOD m]) (hum : u ≡ 1 [ZMOD m])

include hu hum in
theorem add_one_le_left_of_modEq_one : m + 1 ≤ u :=
  add_one_le_of_one_lt_of_modEq_one hu hum

include hx hh hhm hum in
theorem add_one_le_right_of_modEq_one : m + 1 ≤ x :=
  add_one_le_of_one_lt_of_modEq_one hx
    (modEq_one_of_mul_modEq_one hum (by rw [← hh]; exact hhm))

include hm hu hx hh hhm hum in
theorem sq_add_one_le_of_modEq_one : (m + 1) ^ 2 ≤ h := by
  have h₁ : m + 1 ≤ u := add_one_le_left_of_modEq_one hu hum
  have h₂ : m + 1 ≤ x := add_one_le_right_of_modEq_one hx hh hhm hum
  rw [hh]
  nlinarith

include hm hu hx hh hhm hum in
theorem sub_one_lt_ediv_of_modEq_one : m - 1 < (h - 1) / m := by
  have h₁ : m + 1 ≤ u := add_one_le_left_of_modEq_one hu hum
  have h₂ : m + 1 ≤ x := add_one_le_right_of_modEq_one hx hh hhm hum
  have : m + 2 ≤ (h - 1) / m := by
    rw [Int.le_ediv_iff_mul_le (by omega : (0:ℤ) < m), hh]
    nlinarith
  omega

end CongruentProduct

end CFSG.FeitThompson
