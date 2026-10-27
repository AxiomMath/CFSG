module

public import Mathlib.Algebra.Ring.GeomSum

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinaryMersenneOrderPowerTwo

theorem exponent_is_two_power (e : ℕ) (he : 0 < e)
    (h : ∀ r : ℕ, r.Prime → r ∣ 2 ^ e - 1 → ∃ k : ℕ, orderOf (2 : ZMod r) = 2 ^ k) :
    ∃ k : ℕ, e = 2 ^ k := by
  obtain ⟨k, m, hm, hem⟩ := Nat.exists_eq_two_pow_mul_odd he.ne'
  by_cases hm1 : m = 1
  · exact ⟨k, by simp [hem, hm1]⟩
  exfalso
  obtain ⟨l, hl, hlm⟩ := Nat.exists_prime_and_dvd hm1
  have hl2 : l ≠ 2 := by
    rintro rfl
    exact absurd (hm.of_dvd_nat hlm) (by decide)
  have hle : l ∣ e := hem ▸ Dvd.dvd.mul_left hlm _
  have hdvd : 2 ^ l - 1 ∣ 2 ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hle
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hge : 2 ^ 2 ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl.two_le
  obtain ⟨r, hr, hrl⟩ := Nat.exists_prime_and_dvd (show 2 ^ l - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨j, hj⟩ := h r hr (hrl.trans hdvd)
  have h2l : (2 : ZMod r) ^ l = 1 := by
    have : ((2 ^ l - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrl
    rw [Nat.cast_sub (Nat.one_le_two_pow)] at this
    push_cast at this
    exact sub_eq_zero.1 this
  have hord : orderOf (2 : ZMod r) ∣ l := orderOf_dvd_of_pow_eq_one h2l
  rcases (Nat.dvd_prime hl).1 hord with h1 | h1
  · rw [orderOf_eq_one_iff] at h1
    have : (1 : ZMod r) + 1 = 1 + 0 := by rw [one_add_one_eq_two, h1, add_zero]
    exact one_ne_zero (add_left_cancel this)
  · rw [hj] at h1
    have : l ∣ 2 ^ j := h1 ▸ dvd_refl _
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (hl.dvd_of_dvd_pow this))

end CFSG.LinearAlgebra.CoprimeActions.BinaryMersenneOrderPowerTwo
