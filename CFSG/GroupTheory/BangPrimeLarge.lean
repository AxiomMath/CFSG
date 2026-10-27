module

public import CFSG.Timmesfeld.Orders.BangField
public import CFSG.CGT.Timmesfeld75.Sec5ElevenNum

public section

namespace CFSG.GroupTheory

theorem exists_prime_five_le_not_dvd_dvd_two_pow_sub_one {n : ℕ} (h4 : 4 < 2 ^ n)
    (h16 : 2 ^ n ≠ 16) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ¬ r ∣ n ∧ r ∣ 2 ^ n - 1 ∧
      (Odd n ∨ r ∣ 2 ^ (n / 2) - 1) := by
  classical
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n <;> norm_num [Nat.pow_succ] at h4
    · exact hn
  have hn0 : n ≠ 0 := by omega
  set a := n.factorization 2 with ha
  set m := n / 2 ^ a with hm
  have hn_eq : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hm_pos : 0 < m := Nat.ordCompl_pos 2 hn0
  have h2m : ¬ 2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two hn0
  rcases lt_or_eq_of_le (show 1 ≤ m from hm_pos) with hm1 | hm1
  ·
    obtain ⟨r, hprim⟩ :=
      CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (show 2 ≤ m by omega)
        (by intro h6; rw [h6] at h2m; norm_num at h2m)
    have hr : r.Prime := hprim.prime
    have hr5 : 5 ≤ r := hprim.prime.five_le_of_ne_two_of_ne_three (hprim.ne_two (by omega))
      (hprim.three_lt_of_two_lt (by omega)).ne'
    have hrm : ¬ r ∣ m := fun h => absurd (Nat.le_of_dvd (by omega) h)
      (not_le.2 (CFSG.CGT.Timmesfeld75.isPrimitivePrimeDivisor_lt hprim (by omega)))
    have hr2 : r ≠ 2 := hprim.ne_two (by omega)
    have hrn : ¬ r ∣ n := by
      rw [← hn_eq]
      intro h
      rcases (Nat.Prime.dvd_mul hr).mp h with h2' | hm'
      · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2'))
      · exact hrm hm'
    have hdh_of : a ≠ 0 → r ∣ 2 ^ (n / 2) - 1 := by
      intro ha0
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel ha1]
      have hn2 : n / 2 = 2 ^ (a - 1) * m := by
        have hnum : n = (2 ^ (a - 1) * m) * 2 := by
          rw [← hn_eq, h2a]; ring
        rw [hnum]
        exact Nat.mul_div_left _ (by norm_num : 0 < 2)
      have hmn : m ∣ n / 2 := by
        rw [hn2]
        exact dvd_mul_left m (2 ^ (a - 1))
      exact hprim.dvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hmn)
    have hndvd_of : a ≠ 0 → n / 2 ∣ n := by
      intro ha0
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have h2a : 2 ^ a = 2 ^ (a - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel ha1]
      have h2n : 2 ∣ n := by
        refine ⟨2 ^ (a - 1) * m, ?_⟩
        rw [← hn_eq, h2a]
        ring
      exact ⟨2, (Nat.div_mul_cancel h2n).symm⟩
    have hrdvd : r ∣ 2 ^ n - 1 := by
      by_cases ha0 : a = 0
      · have hn_m : n = m := by rw [← hn_eq, ha0]; simp
        simpa [hn_m] using hprim.dvd
      · exact (hdh_of ha0).trans
          (Nat.pow_sub_one_dvd_pow_sub_one 2 (hndvd_of ha0))
    refine ⟨r, hr, hr5, hrn, hrdvd, ?_⟩
    by_cases ha0 : a = 0
    · left
      have hn_m : n = m := by rw [← hn_eq, ha0]; simp
      rw [hn_m]
      exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
    · exact Or.inr (hdh_of ha0)
  ·
    have hn_pow : n = 2 ^ a := by rw [← hn_eq, ← hm1, mul_one]
    have ha3 : 3 ≤ a := by
      have ha2 : 2 ≤ a := by
        by_contra hcon
        have hlt : a < 2 := by omega
        interval_cases a <;> norm_num [hn_pow, Nat.pow_succ] at h4
      have ha_ne2 : a ≠ 2 := by
        intro h
        rw [h] at hn_pow
        norm_num at hn_pow
        exact h16 (by rw [hn_pow]; norm_num)
      omega
    have hk2 : 2 ≤ 2 ^ (a - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk6 : 2 ^ (a - 1) ≠ 6 := by
      intro h6
      have h3dvd : (3 : ℕ) ∣ 2 ^ (a - 1) := by rw [h6]; norm_num
      have h32 : (3 : ℕ) ∣ 2 := Nat.prime_three.dvd_of_dvd_pow h3dvd
      norm_num at h32
    obtain ⟨r, hprim⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hk2 hk6
    have hr : r.Prime := hprim.prime
    have hk3 : 3 ≤ 2 ^ (a - 1) := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (a - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hr5 : 5 ≤ r := hprim.prime.five_le_of_ne_two_of_ne_three (hprim.ne_two (by omega))
      (hprim.three_lt_of_two_lt (by omega)).ne'
    have hr2 : r ≠ 2 := hprim.ne_two (by omega)
    have hrn : ¬ r ∣ n := by
      rw [hn_pow]
      exact fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
        (hr.dvd_of_dvd_pow h))
    have hhalf : n / 2 = 2 ^ (a - 1) := by
      have hnum : n = 2 ^ (a - 1) * 2 := by
        rw [hn_pow, show 2 ^ a = 2 ^ (a - 1) * 2 by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]]
      rw [hnum]
      exact Nat.mul_div_left _ (by norm_num : 0 < 2)
    have hdvd : r ∣ 2 ^ (n / 2) - 1 := by rw [hhalf]; exact hprim.dvd
    have h2n : 2 ∣ n := by rw [hn_pow]; exact dvd_pow_self 2 (by omega)
    have hndvd : n / 2 ∣ n := ⟨2, (Nat.div_mul_cancel h2n).symm⟩
    exact ⟨r, hr, hr5, hrn, hdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hndvd), Or.inr hdvd⟩

theorem dvd_two_pow_sub_one_of_dvd_two_mul {n r : ℕ} (hrdvd : r ∣ 2 ^ n - 1)
    (hhalf : Odd n ∨ r ∣ 2 ^ (n / 2) - 1) : ∀ i : ℕ, n ∣ 2 * i → r ∣ 2 ^ i - 1 := by
  intro i hi
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rcases hhalf with hodd | hh
    · exact absurd hodd (Nat.not_odd_iff_even.2 ⟨k, hk⟩)
    · have hk2 : n / 2 = k := by omega
      have h2k : 2 * k ∣ 2 * i := by rw [show 2 * k = n by omega]; exact hi
      have hki : k ∣ i := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2k
      rw [hk2] at hh
      exact hh.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hki)
  · have hni : n ∣ i := Nat.Coprime.dvd_of_dvd_mul_left hodd.coprime_two_right hi
    exact hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hni)

end CFSG.GroupTheory
