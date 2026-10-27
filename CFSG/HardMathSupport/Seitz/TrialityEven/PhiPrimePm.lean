module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Zify

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

theorem exists_prime_ge_five_dvd_phi_pm {q : ℕ} (hq4 : 4 ≤ q) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h3 : (3 : ℤ) ∣ (q : ℤ) ^ 2 + ε * (q : ℤ) + 1) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ (r : ℤ) ∣ (q : ℤ) ^ 2 + ε * (q : ℤ) + 1 ∧ ¬ r ∣ q := by
  obtain ⟨k, hk1, hN⟩ : ∃ k : ℕ, 1 ≤ k ∧
      (q : ℤ) ^ 2 + ε * (q : ℤ) + 1 = 3 * (3 * (k : ℤ) ^ 2 + 3 * k + 1) := by
    obtain ⟨j, t, ht, hq⟩ : ∃ j t : ℕ, t < 3 ∧ q = 3 * j + t :=
      ⟨q / 3, q % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod q 3).symm⟩
    have hqz : (q : ℤ) = 3 * j + t := by exact_mod_cast hq
    have hform : (q : ℤ) ^ 2 + ε * (q : ℤ) + 1 =
        3 * (3 * (j : ℤ) ^ 2 + 2 * j * t + ε * j) + ((t : ℤ) ^ 2 + ε * t + 1) := by
      rw [hqz]
      ring
    have h3' : (3 : ℤ) ∣ (t : ℤ) ^ 2 + ε * t + 1 := by
      rw [hform] at h3
      exact (dvd_add_right (dvd_mul_right 3 _)).1 h3
    obtain rfl | rfl | rfl : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    · rcases hε with rfl | rfl <;> norm_num at h3'
    · rcases hε with rfl | rfl
      · refine ⟨j, by omega, ?_⟩
        rw [hqz]
        push_cast
        ring
      · norm_num at h3'
    · rcases hε with rfl | rfl
      · norm_num at h3'
      · refine ⟨j, by omega, ?_⟩
        rw [hqz]
        push_cast
        ring
  set j := k * (k + 1) with hj
  have hjeven : Even j := Nat.even_mul_succ_self k
  set m : ℕ := 3 * j + 1 with hm
  have hmz : (m : ℤ) = 3 * (k : ℤ) ^ 2 + 3 * k + 1 := by
    rw [hm, hj]
    push_cast
    ring
  have hm7 : 7 ≤ m := by
    have : 2 ≤ j := by
      have : 1 * 2 ≤ k * (k + 1) := Nat.mul_le_mul hk1 (by omega)
      omega
    omega
  have hmodd : Odd m := by
    obtain ⟨i, hi⟩ := hjeven
    exact ⟨3 * i, by omega⟩
  have hmne : m ≠ 1 := by omega
  set r := m.minFac with hr
  have hrp : r.Prime := Nat.minFac_prime hmne
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hr2 : r ≠ 2 := by
    intro h
    rw [h] at hrm
    exact (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 hrm)
  have hr3 : r ≠ 3 := by
    intro h
    rw [h] at hrm
    omega
  have hr5 : 5 ≤ r := by
    have := hrp.two_le
    have h4 : r ≠ 4 := by
      intro h
      exact absurd (h ▸ hrp) (by decide)
    omega
  have hrN : (r : ℤ) ∣ (q : ℤ) ^ 2 + ε * (q : ℤ) + 1 := by
    rw [hN, ← hmz]
    exact Dvd.dvd.mul_left (by exact_mod_cast hrm) 3
  refine ⟨r, hrp, hr5, hrN, fun hrq => ?_⟩
  have hrq' : (r : ℤ) ∣ (q : ℤ) := by exact_mod_cast hrq
  have h1 : (r : ℤ) ∣ 1 := by
    have e : (q : ℤ) ^ 2 + ε * (q : ℤ) + 1 = (q : ℤ) * ((q : ℤ) + ε) + 1 := by ring
    rw [e] at hrN
    exact (dvd_add_right (dvd_mul_of_dvd_left hrq' _)).1 hrN
  have := Int.eq_one_of_dvd_one (by positivity) h1
  exact hrp.one_lt.ne' (by exact_mod_cast this)

end CFSG.HardMathSupport.Seitz.TrialityEven
