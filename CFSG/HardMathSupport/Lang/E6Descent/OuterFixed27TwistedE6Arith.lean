module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGenArith

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.SeitzReduction.E6Pilot

set_option linter.unusedSimpArgs false in
theorem three_not_dvd_of_mul_eq_twisted (q r : ℕ) (hq2 : 2 ≤ q) (hq : 3 ∣ q + 1)
    (h : r * ((q + 1) ^ 6 * 51840) = numTwistedE6 q) : ¬ 3 ∣ r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3q : ¬ 3 ∣ q := by
    intro h3
    have := (Nat.dvd_add_right h3).1 hq
    omega
  have h3q1 : ¬ 3 ∣ q - 1 := by
    intro h3
    have := Nat.dvd_sub hq h3
    rw [show q + 1 - (q - 1) = 2 by omega] at this
    omega
  have hq0 : q ≠ 0 := by omega
  have hq1 : q + 1 ≠ 0 := by omega
  have hq1' : q - 1 ≠ 0 := by omega
  have hsq : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      have : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
      rw [this]
      simp
    rw [e, padicValNat.mul hq1' hq1, padicValNat.eq_zero_of_not_dvd h3q1, zero_add]
  have h3q2 : ¬ 3 ∣ q ^ 2 := fun h => h3q (Nat.prime_three.dvd_of_dvd_pow h)
  have h3sq : 3 ∣ q ^ 2 - 1 := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      have : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
      rw [this]
      simp
    rw [e]
    exact Dvd.dvd.mul_left hq _
  have hlt : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hev : ∀ n m : ℕ, n = 2 * m → m ≠ 0 →
      padicValNat 3 (q ^ n - 1) = padicValNat 3 (q + 1) + padicValNat 3 m := by
    intro n m hnm hm
    subst hnm
    have := padicValNat.pow_sub_pow (p := 3) (by decide : Odd 3) (x := q ^ 2) (y := 1) hlt h3sq
      h3q2 hm
    rw [one_pow, ← pow_mul, hsq] at this
    exact this
  have hodd : ∀ n : ℕ, Odd n →
      padicValNat 3 (q ^ n + 1) = padicValNat 3 (q + 1) + padicValNat 3 n := by
    intro n hn
    have := padicValNat.pow_add_pow (p := 3) (by decide : Odd 3) (x := q) (y := 1) hq h3q hn
    simpa using this
  have hne : ∀ d : ℕ, d ≠ 0 → q ^ d - 1 ≠ 0 := fun d hd =>
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hd (by omega))
  have hneP : ∀ d : ℕ, q ^ d + 1 ≠ 0 := fun d => Nat.succ_ne_zero _
  have h12 := hne 12 (by norm_num)
  have h8 := hne 8 (by norm_num)
  have h6 := hne 6 (by norm_num)
  have h2 := hne 2 (by norm_num)
  have h9 := hneP 9
  have h5 := hneP 5
  have hnum : padicValNat 3 (numTwistedE6 q) = 6 * padicValNat 3 (q + 1) + 4 := by
    unfold numTwistedE6
    rw [padicValNat.mul (by simp [hq0, h12, h9, h8, h6, h5]) h2,
      padicValNat.mul (by simp [hq0, h12, h9, h8, h6]) h5,
      padicValNat.mul (by simp [hq0, h12, h9, h8]) h6,
      padicValNat.mul (by simp [hq0, h12, h9]) h8,
      padicValNat.mul (by simp [hq0, h12]) h9,
      padicValNat.mul (by simp [hq0]) h12,
      padicValNat.pow _ _, padicValNat.eq_zero_of_not_dvd h3q,
      hev 12 6 (by norm_num) (by norm_num), hodd 9 (by decide), hev 8 4 (by norm_num) (by norm_num),
      hev 6 3 (by norm_num) (by norm_num),
      hodd 5 (by decide), hev 2 1 (by norm_num) (by norm_num)]
    have e6 : padicValNat 3 6 = 1 := by
      rw [show (6 : ℕ) = 3 * 2 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have e9 : padicValNat 3 9 = 2 := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, padicValNat.prime_pow]
    have e4 : padicValNat 3 4 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have e3 : padicValNat 3 3 = 1 := padicValNat.self (by norm_num)
    have e5 : padicValNat 3 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    rw [e6, e9, e4, e3, e5, padicValNat.one]
    ring
  have hX : padicValNat 3 ((q + 1) ^ 6 * 51840) = 6 * padicValNat 3 (q + 1) + 4 := by
    rw [padicValNat.mul (pow_ne_zero _ hq1) (by norm_num), padicValNat.pow _ _,
      show (51840 : ℕ) = 3 ^ 4 * 640 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 640)]
  have hnz : numTwistedE6 q ≠ 0 := by
    unfold numTwistedE6
    simp [hq0, h12, h9, h8, h6, h5, h2]
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hnz (by rw [← h]; simp)
  have hX0 : (q + 1) ^ 6 * 51840 ≠ 0 := mul_ne_zero (pow_ne_zero _ hq1) (by norm_num)
  have hv := congrArg (padicValNat 3) h
  rw [padicValNat.mul hr0 hX0, hnum, hX] at hv
  have hv0 : padicValNat 3 r = 0 := by omega
  intro hdvd
  have := (dvd_iff_padicValNat_ne_zero hr0).1 hdvd
  exact this hv0

end CFSG.HardMathSupport.Lang.E6Descent
