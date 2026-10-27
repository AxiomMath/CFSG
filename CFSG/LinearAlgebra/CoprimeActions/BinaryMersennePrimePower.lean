module


public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimePower

theorem prime_and_odd (e : ℕ) (he : 2 < e) (hr : IsPrimePow (2 ^ e - 1)) :
    Nat.Prime (2 ^ e - 1) ∧ Odd e := by
  have aux_odd_sq_mod8 (x : ℕ) (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
    have h1 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
    rcases h1 with h | h | h | h <;> simp [Nat.pow_mod, h]
  have aux_factor (q : ℤ) (hq : Odd q) (n : ℕ) :
      ∃ Φ : ℤ, Odd Φ ∧ q ^ (2 * n + 1) + 1 = (q + 1) * Φ := by
    induction n with
    | zero => exact ⟨1, odd_one, by ring⟩
    | succ n ih =>
      obtain ⟨Φ, hO, hE⟩ := ih
      refine ⟨q ^ 2 * Φ - (q - 1), ?_, ?_⟩
      · exact (hq.pow.mul hO).sub_even (hq.sub_odd odd_one)
      · have h : q ^ (2 * (n + 1) + 1) = q ^ 2 * q ^ (2 * n + 1) := by ring
        rw [h]
        linear_combination q ^ 2 * hE
  obtain ⟨q, k, hq, hk, hqk⟩ := (isPrimePow_nat_iff _).1 hr
  have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
  have h8 : 2 ^ e % 8 = 0 := by
    obtain ⟨t, rfl⟩ : ∃ t, e = t + 3 := ⟨e - 3, by omega⟩
    rw [pow_add]; simp
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hq2 : q ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
    rw [hqk] at this
    omega
  have hqodd : Odd q := by
    rcases hq.eq_two_or_odd' with h | h
    · exact absurd h hq2
    · exact h
  rcases Nat.even_or_odd' k with ⟨m, hm | hm⟩
  ·
    exfalso
    have hm1 : 1 ≤ m := by omega
    have hodd : (q ^ m) % 2 = 1 := by
      exact Nat.odd_iff.mp hqodd.pow
    have hsq : (q ^ m) ^ 2 % 8 = 1 := aux_odd_sq_mod8 _ hodd
    have hk2 : q ^ k = (q ^ m) ^ 2 := by
      rw [hm, ← pow_mul]; congr 1; ring
    rw [hk2] at hqk
    omega
  ·
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨m, by omega⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    ·
      subst hn
      have hprime : Nat.Prime (2 ^ e - 1) := by
        have : q = 2 ^ e - 1 := by simpa using hqk
        rw [← this]; exact hq
      refine ⟨hprime, ?_⟩
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨j, hj⟩ := hev
      obtain ⟨c, hc⟩ : ∃ c, 2 ^ j = c + 1 := ⟨2 ^ j - 1, by have := Nat.one_le_two_pow (n := j); omega⟩
      have hc3 : 3 ≤ c := by
        have : 4 ≤ 2 ^ j := by
          have hj2 : 2 ≤ j := by omega
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
        omega
      have hE : 2 ^ e = (c + 1) * (c + 1) := by
        rw [hj, pow_add, hc]
      have hfac : 2 ^ e - 1 = c * (c + 2) := by
        have : (c + 1) * (c + 1) = c * (c + 2) + 1 := by ring
        omega
      have hdvd : c ∣ 2 ^ e - 1 := ⟨c + 2, hfac⟩
      rcases hprime.eq_one_or_self_of_dvd c hdvd with h | h
      · omega
      · have : c * (c + 2) = c * 1 := by rw [← hfac, ← h]; ring
        have := Nat.eq_of_mul_eq_mul_left (by omega) this
        omega
    ·
      exfalso
      have h1 : q ^ (2 * n + 1) + 1 = 2 ^ e := by omega
      have h2 : (q : ℤ) ^ (2 * n + 1) + 1 = 2 ^ e := by exact_mod_cast h1
      obtain ⟨Φ, hO, hF⟩ := aux_factor (q : ℤ) (by exact_mod_cast hqodd) n
      have hdvd : Φ ∣ (2 : ℤ) ^ e := ⟨(q : ℤ) + 1, by rw [← h2, hF]; ring⟩
      have hnat : Φ.natAbs ∣ 2 ^ e := by
        have := Int.natAbs_dvd_natAbs.mpr hdvd
        simpa using this
      obtain ⟨i, hi, hΦ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hnat
      have hodd' : Odd Φ.natAbs := Int.natAbs_odd.mpr hO
      have hi0 : i = 0 := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact h
        · exfalso
          have : 2 ∣ Φ.natAbs := by rw [hΦ]; exact dvd_pow_self 2 h.ne'
          rcases hodd' with ⟨r, hr⟩
          omega
      rw [hi0, pow_zero] at hΦ
      have hΦ' : Φ = 1 ∨ Φ = -1 := by
        rcases Int.natAbs_eq Φ with h | h <;> rw [hΦ] at h <;> simp at h <;> simp [h]
      have hq0 : (0 : ℤ) ≤ q := by positivity
      have hqge : (2 : ℤ) ≤ q := by
        have : 2 ≤ q := hq.two_le
        exact_mod_cast this
      have hpow : (q : ℤ) ^ (2 * n + 1) ≥ (q : ℤ) ^ 3 := pow_le_pow_right₀ (by linarith) (by omega)
      have h3 : (q : ℤ) ^ 3 ≥ 4 * q := by
        have : (q : ℤ) ^ 3 = q * q * q := by ring
        nlinarith
      rcases hΦ' with h | h
      · rw [h] at hF
        linarith
      · rw [h] at hF
        nlinarith

end CFSG.LinearAlgebra.CoprimeActions.BinaryMersennePrimePower
