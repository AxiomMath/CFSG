module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.CGT.PushingUpLit.SolK

theorem pow_ge_quad (m : ℕ) (hm : 6 ≤ m) : (m + 3) ^ 2 + 6 ≤ 2 ^ m + 3 * (m + 3) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 2 m]
    nlinarith [ih]

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

theorem counting_ineq (d r : ℕ) (hd : 9 ≤ d) (hr : 1 ≤ r) :
    (1 + (d - 2).choose 2) * r + 1 + d.choose 2 * r < 2 ^ (d - 3) * r := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 3 := ⟨d - 3, by omega⟩
  have hm : 6 ≤ m := by omega
  have h1 := pow_ge_quad m hm
  have h2 := two_mul_choose_two (m + 3 - 2)
  have h3 := two_mul_choose_two (m + 3)
  have e1 : m + 3 - 2 = m + 1 := by omega
  have e2 : m + 3 - 3 = m := by omega
  rw [e1] at h2
  rw [e1, e2]
  have h4 : (m + 1) - 1 = m := by omega
  have h5 : (m + 3) - 1 = m + 2 := by omega
  rw [h4] at h2
  rw [h5] at h3
  have hc : (m + 1).choose 2 + (m + 3).choose 2 + 1 + 2 ≤ 2 ^ m := by nlinarith [h1, h2, h3]
  nlinarith [hc, hr]

end CFSG.CGT.PushingUpLit.SolK
