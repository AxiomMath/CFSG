module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FamilyArith
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeSporOrders

public section

namespace CFSG.EvenSporadicStandard.Induction

open CFSG.Open CFSG.ComponentClassification.CatFC
open scoped Nat

theorem two_pow_six_mul_dvd_ordG2 {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (6 * n) ∣ ordG2 (2 ^ n) := by
  rw [← padicValNat_ordG2 hn]
  exact pow_padicValNat_dvd

theorem ordG2_two_pow_lt {n : ℕ} (hn : 1 ≤ n) : ordG2 (2 ^ n) < 2 ^ (14 * n) := by
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq6 : 64 ≤ (2 ^ n) ^ 6 := by
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ (2 ^ n) ^ 6 := Nat.pow_le_pow_left hq2 6
  have h3 : 0 < (2 ^ n) ^ 6 := by positivity
  have h3' : 0 < (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) := Nat.mul_pos h3 (by omega)
  have h1 : (2 ^ n) ^ 6 - 1 < (2 ^ n) ^ 6 := Nat.sub_one_lt (ne_of_gt h3)
  have h2 : (2 ^ n) ^ 2 - 1 < (2 ^ n) ^ 2 :=
    Nat.sub_one_lt (ne_of_gt (by positivity : 0 < (2 ^ n) ^ 2))
  calc ordG2 (2 ^ n)
      = (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1) := rfl
    _ < (2 ^ n) ^ 6 * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2) :=
        Nat.mul_lt_mul_of_pos_left h2 h3'
    _ < (2 ^ n) ^ 6 * ((2 ^ n) ^ 6) * ((2 ^ n) ^ 2) :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left h1 h3) (by positivity)
    _ = 2 ^ (14 * n) := by
        rw [show 14 * n = n * 6 + n * 6 + n * 2 by ring, pow_add, pow_add]
        simp only [pow_mul]

theorem two_pow_le_factorial (n : ℕ) (hn : 2 ≤ n) : 2 ^ (14 * n + 1) ≤ (6 * n + 2)! := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpow : 2 ^ 14 ≤ (6 * n + 3) ^ 6 := by
      have h15 : 15 ≤ 6 * n + 3 := by omega
      calc 2 ^ 14 = 16384 := by norm_num
        _ ≤ 15 ^ 6 := by norm_num
        _ ≤ (6 * n + 3) ^ 6 := Nat.pow_le_pow_left h15 6
    have hkey : (6 * n + 2)! * (6 * n + 3) ^ 6 ≤ (6 * (n + 1) + 2)! := by
      have h := Nat.factorial_mul_pow_le_factorial (m := 6 * n + 2) (n := 6)
      have e2 : 6 * n + 2 + 1 = 6 * n + 3 := by ring
      have e : 6 * n + 2 + 6 = 6 * (n + 1) + 2 := by ring
      rw [e2, e] at h
      exact h
    calc 2 ^ (14 * (n + 1) + 1)
        = 2 ^ 14 * 2 ^ (14 * n + 1) := by
          have e : 14 * (n + 1) + 1 = 14 + (14 * n + 1) := by ring
          rw [e, pow_add]
      _ ≤ 2 ^ 14 * (6 * n + 2)! := Nat.mul_le_mul_left _ ih
      _ ≤ (6 * n + 3) ^ 6 * (6 * n + 2)! := Nat.mul_le_mul_right _ hpow
      _ ≤ (6 * n + 2)! * (6 * n + 3) ^ 6 := by rw [mul_comm]
      _ ≤ (6 * (n + 1) + 2)! := hkey

theorem ordG2_two_pow_ne_factorial_div_two {n k : ℕ} (hn : 2 ≤ n) (hk : 5 ≤ k) :
    ordG2 (2 ^ n) ≠ Nat.factorial k / 2 := by
  intro h
  have hn1 : 1 ≤ n := by omega
  have hk2 : 2 ≤ k := by omega
  have hdvd : 2 ∣ k ! := Nat.dvd_factorial (by norm_num) hk2
  have hfact : k ! = 2 * ordG2 (2 ^ n) := by
    rw [h, Nat.mul_div_cancel' hdvd]
  have hdvd2 : 2 ^ (6 * n + 1) ∣ k ! := by
    rw [hfact, pow_succ']
    exact Nat.mul_dvd_mul_left 2 (two_pow_six_mul_dvd_ordG2 hn1)
  have hlt : 6 * n + 1 < k := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show k ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd2
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hkge : 6 * n + 2 ≤ k := by omega
  have hle_fact : (6 * n + 2)! ≤ k ! := Nat.factorial_le hkge
  have hlow : 2 ^ (14 * n + 1) ≤ (6 * n + 2)! := two_pow_le_factorial n hn
  have hupp : k ! < 2 ^ (14 * n + 1) := by
    rw [hfact]
    calc 2 * ordG2 (2 ^ n) < 2 * 2 ^ (14 * n) :=
          Nat.mul_lt_mul_of_pos_left (ordG2_two_pow_lt hn1) (by norm_num)
      _ = 2 ^ (14 * n + 1) := by rw [pow_succ']
  omega

theorem not_two_pow_42_dvd_sporOrd (s : TauCeti.SporadicName) (hs : s ≠ .M) :
    ¬ 2 ^ 42 ∣ CFSG.AGLEmbedding.sporOrd s := by
  cases s <;> first
    | exact absurd rfl hs
    | (simp only [CFSG.AGLEmbedding.sporOrd]; decide)

theorem g2_inner_row {n : ℕ} (hn : 2 ≤ n) {s : TauCeti.SporadicName}
    (hdvd : ordG2 (2 ^ n) ∣ CFSG.AGLEmbedding.sporOrd s)
    (hrow : SporadicInnerRow s (ordG2 (2 ^ n))) : s = .Co1 ∧ n = 2 := by
  have h6n : 6 * n ≤ 41 := by
    by_contra hcon
    have h42 : 42 ≤ 6 * n := by omega
    have hpow : 2 ^ 42 ∣ ordG2 (2 ^ n) :=
      (Nat.pow_dvd_pow 2 h42).trans (two_pow_six_mul_dvd_ordG2 (by omega))
    by_cases hsM : s = .M
    · rw [hsM] at hrow
      simp only [SporadicInnerRow] at hrow
      exact hrow.2 hpow
    · exact not_two_pow_42_dvd_sporOrd s hsM (hpow.trans hdvd)
  have hn6 : n ≤ 6 := by omega
  interval_cases n <;>
    cases s <;>
    simp only [SporadicInnerRow, CFSG.AGLEmbedding.sporOrd, ordG2] at hrow hdvd ⊢ <;>
    first
      | decide
      | exact absurd hrow (by decide)
      | exact absurd hdvd (by decide)

theorem g2_outer_row {n : ℕ} (hn : 2 ≤ n) {s : TauCeti.SporadicName}
    (hdvd : ordG2 (2 ^ n) ∣ CFSG.AGLEmbedding.sporOrd s)
    (hrow : SporadicOuterRow s (ordG2 (2 ^ n))) : False := by
  have h6n : 6 * n ≤ 41 := by
    by_contra hcon
    have h42 : 42 ≤ 6 * n := by omega
    have hpow : 2 ^ 42 ∣ ordG2 (2 ^ n) :=
      (Nat.pow_dvd_pow 2 h42).trans (two_pow_six_mul_dvd_ordG2 (by omega))
    by_cases hsM : s = .M
    · rw [hsM] at hrow
      simpa only [SporadicOuterRow] using hrow
    · exact not_two_pow_42_dvd_sporOrd s hsM (hpow.trans hdvd)
  have hn6 : n ≤ 6 := by omega
  interval_cases n <;>
    cases s <;>
    simp only [SporadicOuterRow, CFSG.AGLEmbedding.sporOrd, ordG2] at hrow hdvd ⊢ <;>
    first
      | exact absurd hrow (by decide)
      | exact absurd hdvd (by decide)

end CFSG.EvenSporadicStandard.Induction
