module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Zify
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

theorem gomiOdd_eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h]
  obtain ⟨m, hm⟩ := (Nat.even_mul_succ_self k).two_dvd
  exact ⟨m, by rw [hm]; ring⟩

theorem gomiOdd_sixteen_dvd_pow_four_sub_one {q : ℕ} (hq : Odd q) : 16 ∣ q ^ 4 - 1 := by
  obtain ⟨c, hc⟩ := gomiOdd_eight_dvd_sq_sub_one hq
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (hq.pos)
  have h1 : q ^ 2 = 8 * c + 1 := by omega
  have h2 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    apply Nat.sub_eq_of_eq_add
    have : q ^ 4 = (q ^ 2) ^ 2 := by ring
    rw [this]
    have h3 : (q ^ 2 - 1) * (q ^ 2 + 1) + 1 = (q ^ 2) ^ 2 := by
      zify [hq2]
      ring
    omega
  rw [h2, hc, h1]
  exact ⟨c * (4 * c + 1), by ring⟩

theorem gomiOdd_sub_one_dvd_pow_sub_one (q j : ℕ) : q - 1 ∣ q ^ j - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 j

theorem gomiOdd_sq_sub_one_dvd_pow_two_mul (q j : ℕ) : q ^ 2 - 1 ∣ q ^ (2 * j) - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 j
  simpa [← pow_mul] using this

theorem gomiOdd_pow_four_sub_one_dvd_pow_four_mul (q j : ℕ) : q ^ 4 - 1 ∣ q ^ (4 * j) - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (q ^ 4) 1 j
  simpa [← pow_mul] using this

theorem gomiOdd_add_one_dvd_pow_add_one (q : ℕ) {j : ℕ} (hj : Odd j) : q + 1 ∣ q ^ j + 1 := by
  simpa using Odd.nat_add_dvd_pow_add_pow q 1 hj

theorem gomiOdd_two_dvd_pow_sub_one {q : ℕ} (hq : Odd q) (j : ℕ) : 2 ∣ q ^ j - 1 := by
  have h1 : 2 ∣ q - 1 := by
    obtain ⟨k, rfl⟩ := hq
    exact ⟨k, by omega⟩
  exact h1.trans (gomiOdd_sub_one_dvd_pow_sub_one q j)

theorem gomiOdd_two_dvd_pow_add_one {q : ℕ} (hq : Odd q) (j : ℕ) : 2 ∣ q ^ j + 1 := by
  have := (hq.pow (n := j))
  obtain ⟨k, hk⟩ := this
  exact ⟨k + 1, by omega⟩

theorem gomiOdd_pow_dvd_div_of_dvd_two_pow {X g k e : ℕ} (hg : g ∣ 2 ^ e)
    (hX : 2 ^ (k + e) ∣ X) : 2 ^ k ∣ X / g := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hg
  obtain ⟨m, rfl⟩ := hX
  have h1 : 2 ^ (k + e) * m = 2 ^ j * (2 ^ (k + e - j) * m) := by
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [h1, Nat.mul_div_cancel_left _ (by positivity)]
  exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem gomiOdd_pow_dvd_div_of_odd {X g k : ℕ} (hgX : g ∣ X) (hg : Odd g)
    (hX : 2 ^ k ∣ X) : 2 ^ k ∣ X / g := by
  obtain ⟨m, hm⟩ := hgX
  have hg0 : 0 < g := hg.pos
  rw [hm, Nat.mul_div_cancel_left _ hg0]
  rw [hm] at hX
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hg)).dvd_of_dvd_mul_left hX

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
