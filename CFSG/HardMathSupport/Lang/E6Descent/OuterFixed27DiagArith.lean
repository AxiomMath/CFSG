module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.SeitzReduction.E6Pilot

theorem three_not_dvd_of_mul_eq (q r : ℕ) (hq2 : 2 ≤ q) (hq : 3 ∣ q - 1)
    (h : r * ((q - 1) ^ 6 * 51840) = numE6 q) : ¬ 3 ∣ r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3q : ¬ 3 ∣ q := by
    intro h3
    have := Nat.dvd_sub h3 hq
    rw [show q - (q - 1) = 1 by omega] at this
    omega
  have hpow : ∀ d : ℕ, d ≠ 0 →
      padicValNat 3 (q ^ d - 1) = padicValNat 3 (q - 1) + padicValNat 3 d := by
    intro d hd
    have := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := q) (y := 1) hq2 hq h3q hd
    simpa using this
  have hne : ∀ d : ℕ, d ≠ 0 → q ^ d - 1 ≠ 0 := fun d hd =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
  have hq0 : q ≠ 0 := by omega
  have hq1 : q - 1 ≠ 0 := by omega
  have h12 := hne 12 (by norm_num)
  have h9 := hne 9 (by norm_num)
  have h8 := hne 8 (by norm_num)
  have h6 := hne 6 (by norm_num)
  have h5 := hne 5 (by norm_num)
  have h2 := hne 2 (by norm_num)
  have hnum : padicValNat 3 (numE6 q) = 6 * padicValNat 3 (q - 1) + 4 := by
    unfold numE6
    rw [padicValNat.mul (by simp [hq0, h12, h9, h8, h6, h5]) h2,
      padicValNat.mul (by simp [hq0, h12, h9, h8, h6]) h5,
      padicValNat.mul (by simp [hq0, h12, h9, h8]) h6,
      padicValNat.mul (by simp [hq0, h12, h9]) h8,
      padicValNat.mul (by simp [hq0, h12]) h9,
      padicValNat.mul (by simp [hq0]) h12,
      padicValNat.pow _ _, padicValNat.eq_zero_of_not_dvd h3q,
      hpow 12 (by norm_num), hpow 9 (by norm_num), hpow 8 (by norm_num), hpow 6 (by norm_num),
      hpow 5 (by norm_num), hpow 2 (by norm_num)]
    have e12 : padicValNat 3 12 = 1 := by
      rw [show (12 : ℕ) = 3 * 4 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have e9 : padicValNat 3 9 = 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, padicValNat.prime_pow]
    have e8 : padicValNat 3 8 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have e6 : padicValNat 3 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have e5 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have e2 : padicValNat 3 2 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    rw [e12, e9, e8, e6, e5, e2]
    ring
  have hX : padicValNat 3 ((q - 1) ^ 6 * 51840) = 6 * padicValNat 3 (q - 1) + 4 := by
    rw [padicValNat.mul (pow_ne_zero _ hq1) (by norm_num), padicValNat.pow _ _,
      show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 640)]
  have hnz : numE6 q ≠ 0 := by
    unfold numE6
    simp [hq0, h12, h9, h8, h6, h5, h2]
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hnz (by rw [← h]; simp)
  have hX0 : (q - 1) ^ 6 * 51840 ≠ 0 := mul_ne_zero (pow_ne_zero _ hq1) (by norm_num)
  have hv := congrArg (padicValNat 3) h
  rw [padicValNat.mul hr0 hX0, hnum, hX] at hv
  have hv0 : padicValNat 3 r = 0 := by omega
  intro hdvd
  have := (dvd_iff_padicValNat_ne_zero hr0).1 hdvd
  exact this hv0

end CFSG.HardMathSupport.Lang.E6Descent
