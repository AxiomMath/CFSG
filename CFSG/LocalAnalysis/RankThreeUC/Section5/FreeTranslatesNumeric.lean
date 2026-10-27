module

public import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates

theorem sq_succ_lt_two_pow_succ {n : ℕ} (hn : 4 ≤ n) : (n + 1) ^ 2 < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 (n + 1)]
    nlinarith

theorem sq_succ_le_two_pow {n : ℕ} (hn : 6 ≤ n) : (n + 1) ^ 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ 2 n]
    nlinarith

theorem three_dvd_two_pow_sub_one_of_even {e : ℕ} (he : Even e) : 3 ∣ 2 ^ e - 1 := by
  have := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp he)
  simpa using this

theorem nine_le_of_odd_not_isPrimePow {e : ℕ} (he : 2 < e) (hodd : Odd e)
    (hpp : ¬ IsPrimePow (2 ^ e - 1)) : 9 ≤ e := by
  by_contra hlt
  obtain ⟨m, rfl⟩ := hodd
  have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm with rfl | rfl | rfl
  · exact hpp (by
      have : (2 : ℕ) ^ (2 * 1 + 1) - 1 = 7 := by norm_num
      rw [this]
      exact (by norm_num : Nat.Prime 7).isPrimePow)
  · exact hpp (by
      have : (2 : ℕ) ^ (2 * 2 + 1) - 1 = 31 := by norm_num
      rw [this]
      exact (by norm_num : Nat.Prime 31).isPrimePow)
  · exact hpp (by
      have : (2 : ℕ) ^ (2 * 3 + 1) - 1 = 127 := by norm_num
      rw [this]
      exact (by norm_num : Nat.Prime 127).isPrimePow)

theorem exists_prime_mul_sq_lt {e p k N : ℕ} (he : 2 < e) (hpp : ¬ IsPrimePow (2 ^ e - 1))
    (hp : p.Prime) (hp2 : p ≠ 2) (hpe : ¬ p ∣ 2 ^ e - 1) (hk : k ≤ e + 1) (hk5 : 5 ≤ p → 2 * k ≤ e + 1)
    (hN : 2 ^ e ≤ N) (hNodd : Odd e → 4 ^ e ≤ N) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ e - 1 ∧ (r - 1) * k ^ 2 < N := by
  rcases Nat.even_or_odd e with heven | hodd
  ·
    have h3 := three_dvd_two_pow_sub_one_of_even heven
    refine ⟨3, Nat.prime_three, h3, ?_⟩
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hpe h3
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      by_contra hlt
      have : p = 3 ∨ p = 4 := by omega
      rcases this with h | h
      · exact hp3 h
      · exact absurd hp (by rw [h]; norm_num)
    have h2k := hk5 hp5
    have he4 : 4 ≤ e := by
      obtain ⟨m, rfl⟩ := heven
      omega
    have hlt := sq_succ_lt_two_pow_succ he4
    rw [pow_succ 2 e] at hlt
    have hsq : (2 * k) ^ 2 ≤ (e + 1) ^ 2 := Nat.pow_le_pow_left h2k 2
    show (3 - 1) * k ^ 2 < N
    nlinarith
  ·
    have he9 := nine_le_of_odd_not_isPrimePow he hodd hpp
    have h2e : 512 ≤ 2 ^ e := by
      calc 512 = 2 ^ 9 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he9
    have hne1 : 2 ^ e - 1 ≠ 1 := by omega
    have hr := Nat.minFac_prime hne1
    have hrd := Nat.minFac_dvd (2 ^ e - 1)
    have hrle : (2 ^ e - 1).minFac ≤ 2 ^ e - 1 := Nat.le_of_dvd (by omega) hrd
    refine ⟨(2 ^ e - 1).minFac, hr, hrd, ?_⟩
    have hsq : k ^ 2 ≤ 2 ^ e :=
      (Nat.pow_le_pow_left hk 2).trans (sq_succ_le_two_pow (by omega))
    have h4 : 4 ^ e = 2 ^ e * 2 ^ e := by
      rw [← mul_pow]
      norm_num
    calc ((2 ^ e - 1).minFac - 1) * k ^ 2 ≤ ((2 ^ e - 1).minFac - 1) * 2 ^ e :=
          Nat.mul_le_mul_left _ hsq
      _ < 2 ^ e * 2 ^ e := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = 4 ^ e := h4.symm
      _ ≤ N := hNodd hodd

end CFSG.LocalAnalysis.RankThreeUC.Section5.FreeTranslates
