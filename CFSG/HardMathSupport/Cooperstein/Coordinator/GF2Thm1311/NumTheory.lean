module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311

theorem two_pow_mod_nine (j : ℕ) : 2 ^ j % 9 = 1 ∨ 2 ^ j % 9 = 2 ∨ 2 ^ j % 9 = 4 ∨
    2 ^ j % 9 = 5 ∨ 2 ^ j % 9 = 7 ∨ 2 ^ j % 9 = 8 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; omega

theorem two_pow_mod_seven (j : ℕ) : 2 ^ j % 7 = 1 ∨ 2 ^ j % 7 = 2 ∨ 2 ^ j % 7 = 4 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ]; omega

theorem exists_prime_dvd_sq_sub_add_one (j : ℕ) (hj : 2 ≤ j) :
    ∃ p, p.Prime ∧ 11 ≤ p ∧ p ∣ 2 ^ (2 * j) - 2 ^ j + 1 := by
  set x := 2 ^ j with hx
  have hx4 : 4 ≤ x := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hxx : 2 ^ (2 * j) = x * x := by rw [hx, ← pow_add]; ring_nf
  rw [hxx]
  set N := x * x - x + 1 with hN
  have hNx : N + x = x * x + 1 := by
    have : x ≤ x * x := Nat.le_mul_self x
    omega
  have hN13 : 13 ≤ N := by nlinarith
  have hxe : x % 2 = 0 := by
    rw [hx]; exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have hN2 : N % 2 = 1 := by
    have h1 : x * x % 2 = 0 := by rw [Nat.mul_mod, hxe]
    omega
  have hN5 : N % 5 ≠ 0 := by
    have h1 : x * x % 5 = (x % 5) * (x % 5) % 5 := Nat.mul_mod x x 5
    have h2 : x % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases h : x % 5 <;> omega
  have hN7 : N % 7 ≠ 0 := by
    have h1 : x * x % 7 = (x % 7) * (x % 7) % 7 := Nat.mul_mod x x 7
    have h7 := two_pow_mod_seven j
    rw [← hx] at h7
    rcases h7 with h | h | h <;> rw [h] at h1 <;> omega
  have hN9 : N % 9 ≠ 0 := by
    have h1 : x * x % 9 = (x % 9) * (x % 9) % 9 := Nat.mul_mod x x 9
    have h9 := two_pow_mod_nine j
    rw [← hx] at h9
    rcases h9 with h | h | h | h | h | h <;> rw [h] at h1 <;> omega
  by_contra hcon
  push Not at hcon
  have hq : ∀ q : ℕ, q.Prime → q ∣ N → q = 3 := by
    intro q hqp hqd
    have hqle : q ≤ 10 := by
      by_contra h; exact hcon q hqp (by omega) hqd
    interval_cases q
    · exact absurd hqp (by decide)
    · exact absurd hqp (by decide)
    · omega
    · rfl
    · exact absurd hqp (by decide)
    · omega
    · exact absurd hqp (by decide)
    · omega
    · exact absurd hqp (by decide)
    · exact absurd hqp (by decide)
    · exact absurd hqp (by decide)
  have hNpos : N ≠ 0 := by omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hNpos (fun hd hdp => hq _ hd hdp)
  obtain ⟨a, ha⟩ : ∃ a, N = 3 ^ a := ⟨_, hpow⟩
  rcases Nat.lt_or_ge a 2 with h | h
  · interval_cases a <;> simp at ha <;> omega
  · have : 9 ∣ N := by
      rw [ha]
      calc 9 = 3 ^ 2 := by norm_num
        _ ∣ 3 ^ a := pow_dvd_pow 3 h
    omega



theorem exists_good_prime_three (j : ℕ) (hj : 2 ≤ j) :
    ∃ p, p.Prime ∧ 11 ≤ p ∧ p ∣ (2 ^ j) ^ 3 + 1 ∧ ¬ p ∣ 2 ^ (2 * j) - 1 := by
  obtain ⟨p, hp, hp11, hpd⟩ := exists_prime_dvd_sq_sub_add_one j hj
  refine ⟨p, hp, hp11, ?_, ?_⟩
  · have hx : 2 ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [← pow_add]; ring_nf
    rw [hx] at hpd
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h2 : 2 ^ j ≤ 2 ^ j * 2 ^ j := Nat.le_mul_self _
    have : (2 ^ j) ^ 3 + 1 = (2 ^ j + 1) * (2 ^ j * 2 ^ j - 2 ^ j + 1) := by
      zify [h2]
      ring
    rw [this]
    exact Dvd.dvd.mul_left hpd _
  · intro hdvd
    have hx : 2 ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [← pow_add]; ring_nf
    rw [hx] at hpd hdvd
    set x := 2 ^ j with hxdef
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have h2 : x ≤ x * x := Nat.le_mul_self _
    have : Fact p.Prime := ⟨hp⟩
    have hN : ((x * x - x + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpd
    have hM : ((x * x - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    have hx11 : 1 ≤ x * x := le_trans hx1 h2
    push_cast [Nat.cast_sub h2, Nat.cast_sub hx11] at hN hM
    have e1 : (x : ZMod p) * x = 1 := by linear_combination hM
    have e2 : (x : ZMod p) = 2 := by linear_combination -hN + e1
    have e3 : (3 : ZMod p) = 0 := by
      rw [e2] at e1
      linear_combination e1
    have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast e3
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega

theorem good_prime_two : Nat.Prime 11 ∧ 11 ≤ 11 ∧ 11 ∣ (2 ^ 1) ^ 5 + 1 ∧ ¬ 11 ∣ 2 ^ (2 * 1) - 1 := by
  refine ⟨by decide, le_rfl, by norm_num, by norm_num⟩

end CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311
