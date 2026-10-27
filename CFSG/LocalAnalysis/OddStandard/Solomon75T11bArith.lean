module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.OddStandard.Solomon75

theorem dvd_of_factorization_eq_eight {N : ℕ} (hN : N ≠ 0) (h : N.factorization 2 = 8) :
    2 ^ 8 ∣ N ∧ ¬ 2 ^ 9 ∣ N := by
  constructor
  · have := Nat.ordProj_dvd N 2
    rwa [h] at this
  · have := Nat.pow_succ_factorization_not_dvd hN Nat.prime_two
    rwa [h] at this

theorem modEq_pred {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD m]) :
    a - 1 ≡ b - 1 [MOD m] := by
  have h1 : (a - 1) + 1 ≡ (b - 1) + 1 [MOD m] := by
    rwa [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb]
  exact Nat.ModEq.add_right_cancel' 1 h1

theorem residue_of_factorization_eight {M : ℕ → ℕ} {k q N : ℕ} (hk : k ≤ 2)
    (hM : ∀ a b, 1 ≤ a → 1 ≤ b → a ≡ b [MOD 2048] → M a ≡ M b [MOD 2048])
    (hq : q % 2 = 1) (hN : N * 2 ^ k = M q) (hMne : M q ≠ 0) (h8 : N.factorization 2 = 8) :
    2 ^ (8 + k) ∣ M (q % 2048) ∧ ¬ 2 ^ (9 + k) ∣ M (q % 2048) := by
  have hNne : N ≠ 0 := by
    rintro rfl
    simp at hN
    exact hMne hN.symm
  obtain ⟨h1, h2⟩ := dvd_of_factorization_eq_eight hNne h8
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hdvd1 : 2 ^ (8 + k) ∣ M q := by
    rw [← hN, pow_add]
    exact Nat.mul_dvd_mul_right h1 _
  have hdvd2 : ¬ 2 ^ (9 + k) ∣ M q := by
    intro h
    rw [← hN, pow_add] at h
    exact h2 (Nat.dvd_of_mul_dvd_mul_right hpos h)
  have hq1 : 1 ≤ q := by omega
  have hr : (q % 2048) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 2048)]
    exact hq
  have hr1 : 1 ≤ q % 2048 := by omega
  have hqr : q ≡ q % 2048 [MOD 2048] := (Nat.mod_modEq q 2048).symm
  have hMqr := hM q (q % 2048) hq1 hr1 hqr
  have hd1 : 2 ^ (8 + k) ∣ 2048 := by
    have : 2 ^ (8 + k) ∣ 2 ^ 11 := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  have hd2 : 2 ^ (9 + k) ∣ 2048 := by
    have : 2 ^ (9 + k) ∣ 2 ^ 11 := Nat.pow_dvd_pow 2 (by omega)
    simpa using this
  exact ⟨(hMqr.dvd_iff hd1).1 hdvd1, fun h => hdvd2 ((hMqr.dvd_iff hd2).2 h)⟩

theorem residue_of_factorization_eight_odd {M : ℕ → ℕ} {D q N : ℕ}
    (hM : ∀ a b, 1 ≤ a → 1 ≤ b → a ≡ b [MOD 2048] → M a ≡ M b [MOD 2048])
    (hq : q % 2 = 1) (hD : D % 2 = 1) (hN : N * D = M q) (hMne : M q ≠ 0)
    (h8 : N.factorization 2 = 8) :
    2 ^ 8 ∣ M (q % 2048) ∧ ¬ 2 ^ 9 ∣ M (q % 2048) := by
  have hNne : N ≠ 0 := by
    rintro rfl
    simp at hN
    exact hMne hN.symm
  obtain ⟨h1, h2⟩ := dvd_of_factorization_eq_eight hNne h8
  have hcop : Nat.Coprime (2 ^ 9) D := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hD
  have hdvd1 : 2 ^ 8 ∣ M q := by
    rw [← hN]
    exact Dvd.dvd.mul_right h1 _
  have hdvd2 : ¬ 2 ^ 9 ∣ M q := by
    intro h
    rw [← hN] at h
    exact h2 (hcop.dvd_of_dvd_mul_right h)
  have hq1 : 1 ≤ q := by omega
  have hr : (q % 2048) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd q (by norm_num : 2 ∣ 2048)]
    exact hq
  have hr1 : 1 ≤ q % 2048 := by omega
  have hqr : q ≡ q % 2048 [MOD 2048] := (Nat.mod_modEq q 2048).symm
  have hMqr := hM q (q % 2048) hq1 hr1 hqr
  have hd1 : 2 ^ 8 ∣ 2048 := by norm_num
  have hd2 : 2 ^ 9 ∣ 2048 := by norm_num
  exact ⟨(hMqr.dvd_iff hd1).1 hdvd1, fun h => hdvd2 ((hMqr.dvd_iff hd2).2 h)⟩

@[expose] def mPSL4 (q : ℕ) : ℕ := q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)))

theorem mPSL4_congr (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD 2048]) :
    mPSL4 a ≡ mPSL4 b [MOD 2048] := by
  have p2 : ∀ i, a ^ i - 1 ≡ b ^ i - 1 [MOD 2048] := fun i =>
    modEq_pred (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hb) (h.pow i)
  unfold mPSL4
  exact (h.pow 6).mul ((p2 2).mul ((p2 3).mul (p2 4)))

theorem res_PSL4_k1 : ∀ r < 2048, r % 2 = 1 → (r % 8 = 3 ∨ r % 8 = 7) →
    ¬ (2 ^ 9 ∣ mPSL4 r ∧ ¬ 2 ^ 10 ∣ mPSL4 r) := by
  decide +kernel

theorem res_PSL4_k2 : ∀ r < 2048, r % 8 = 5 →
    ¬ (2 ^ 10 ∣ mPSL4 r ∧ ¬ 2 ^ 11 ∣ mPSL4 r) := by
  decide +kernel

theorem mPSL4_ne_zero {q : ℕ} (hq : 3 ≤ q) : mPSL4 q ≠ 0 := by
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 1 ≤ q ^ 3 - 1 := by
    have := Nat.pow_le_pow_left hq 3
    omega
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq 4
    omega
  unfold mPSL4
  positivity

theorem not_eight_PSL4 {q N : ℕ} (hq : q % 2 = 1) (h8 : q % 8 ≠ 1)
    (hN : N * Nat.gcd 4 (q - 1) = mPSL4 q) : N.factorization 2 ≠ 8 := by
  intro hf
  have hq3 : 3 ≤ q := by omega
  have hne := mPSL4_ne_zero hq3
  by_cases h5 : q % 8 = 5
  · have hg : Nat.gcd 4 (q - 1) = 2 ^ 2 := by
      rw [Nat.gcd_rec]
      have : (q - 1) % 4 = 0 := by omega
      rw [this]; decide
    rw [hg] at hN
    obtain ⟨h1, h2⟩ :=
      residue_of_factorization_eight (k := 2) (by omega) mPSL4_congr hq hN hne hf
    exact res_PSL4_k2 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h1, h2⟩
  · have hg : Nat.gcd 4 (q - 1) = 2 ^ 1 := by
      rw [Nat.gcd_rec]
      have : (q - 1) % 4 = 2 := by omega
      rw [this]; decide
    rw [hg] at hN
    obtain ⟨h1, h2⟩ :=
      residue_of_factorization_eight (k := 1) (by omega) mPSL4_congr hq hN hne hf
    exact res_PSL4_k1 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) ⟨h1, h2⟩

@[expose] def mPSU4 (q : ℕ) : ℕ := q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)))

theorem mPSU4_congr (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD 2048]) :
    mPSU4 a ≡ mPSU4 b [MOD 2048] := by
  have p2 : ∀ i, a ^ i - 1 ≡ b ^ i - 1 [MOD 2048] := fun i =>
    modEq_pred (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hb) (h.pow i)
  have p3 : ∀ i, a ^ i + 1 ≡ b ^ i + 1 [MOD 2048] := fun i => (h.pow i).add_right 1
  unfold mPSU4
  exact (h.pow 6).mul ((p2 2).mul ((p3 3).mul (p2 4)))

theorem res_PSU4_k1 : ∀ r < 2048, r % 2 = 1 → (r % 8 = 1 ∨ r % 8 = 5) →
    ¬ (2 ^ 9 ∣ mPSU4 r ∧ ¬ 2 ^ 10 ∣ mPSU4 r) := by
  decide +kernel

theorem res_PSU4_k2 : ∀ r < 2048, r % 8 = 3 →
    ¬ (2 ^ 10 ∣ mPSU4 r ∧ ¬ 2 ^ 11 ∣ mPSU4 r) := by
  decide +kernel

theorem mPSU4_ne_zero {q : ℕ} (hq : 3 ≤ q) : mPSU4 q ≠ 0 := by
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq 4
    omega
  unfold mPSU4
  positivity

theorem not_eight_PSU4 {q N : ℕ} (hq : q % 2 = 1) (h8 : q % 8 ≠ 7) (hq3 : 3 ≤ q)
    (hN : N * Nat.gcd 4 (q + 1) = mPSU4 q) : N.factorization 2 ≠ 8 := by
  intro hf
  have hne := mPSU4_ne_zero hq3
  by_cases h3 : q % 8 = 3
  · have hg : Nat.gcd 4 (q + 1) = 2 ^ 2 := by
      rw [Nat.gcd_rec]
      have : (q + 1) % 4 = 0 := by omega
      rw [this]; decide
    rw [hg] at hN
    obtain ⟨h1, h2⟩ :=
      residue_of_factorization_eight (k := 2) (by omega) mPSU4_congr hq hN hne hf
    exact res_PSU4_k2 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h1, h2⟩
  · have hg : Nat.gcd 4 (q + 1) = 2 ^ 1 := by
      rw [Nat.gcd_rec]
      have : (q + 1) % 4 = 2 := by omega
      rw [this]; decide
    rw [hg] at hN
    obtain ⟨h1, h2⟩ :=
      residue_of_factorization_eight (k := 1) (by omega) mPSU4_congr hq hN hne hf
    exact res_PSU4_k1 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) (by omega) ⟨h1, h2⟩

@[expose] def mPSL5 (q : ℕ) : ℕ :=
  q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * ((q ^ 4 - 1) * (q ^ 5 - 1))))

theorem mPSL5_congr (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD 2048]) :
    mPSL5 a ≡ mPSL5 b [MOD 2048] := by
  have p2 : ∀ i, a ^ i - 1 ≡ b ^ i - 1 [MOD 2048] := fun i =>
    modEq_pred (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hb) (h.pow i)
  unfold mPSL5
  exact (h.pow 10).mul ((p2 2).mul ((p2 3).mul ((p2 4).mul (p2 5))))

theorem res_PSL5 : ∀ r < 2048, r % 4 = 3 → ¬ (2 ^ 8 ∣ mPSL5 r ∧ ¬ 2 ^ 9 ∣ mPSL5 r) := by
  decide +kernel

theorem mPSL5_ne_zero {q : ℕ} (hq : 3 ≤ q) : mPSL5 q ≠ 0 := by
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 1 ≤ q ^ 3 - 1 := by
    have := Nat.pow_le_pow_left hq 3
    omega
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq 4
    omega
  have h5 : 1 ≤ q ^ 5 - 1 := by
    have := Nat.pow_le_pow_left hq 5
    omega
  unfold mPSL5
  positivity

theorem not_eight_PSL5 {q N : ℕ} (hq : q % 4 = 3)
    (hN : N * Nat.gcd 5 (q - 1) = mPSL5 q) : N.factorization 2 ≠ 8 := by
  intro hf
  have hq3 : 3 ≤ q := by omega
  have hne := mPSL5_ne_zero hq3
  have hD : Nat.gcd 5 (q - 1) % 2 = 1 := by
    have hd : Nat.gcd 5 (q - 1) ∣ 5 := Nat.gcd_dvd_left _ _
    have : Odd (Nat.gcd 5 (q - 1)) := Odd.of_dvd_nat (by decide) hd
    exact Nat.odd_iff.mp this
  obtain ⟨h1, h2⟩ := residue_of_factorization_eight_odd mPSL5_congr (by omega) hD hN hne hf
  exact res_PSL5 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h1, h2⟩

@[expose] def mPSU5 (q : ℕ) : ℕ :=
  q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1))))

theorem mPSU5_congr (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD 2048]) :
    mPSU5 a ≡ mPSU5 b [MOD 2048] := by
  have p2 : ∀ i, a ^ i - 1 ≡ b ^ i - 1 [MOD 2048] := fun i =>
    modEq_pred (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hb) (h.pow i)
  have p3 : ∀ i, a ^ i + 1 ≡ b ^ i + 1 [MOD 2048] := fun i => (h.pow i).add_right 1
  unfold mPSU5
  exact (h.pow 10).mul ((p2 2).mul ((p3 3).mul ((p2 4).mul (p3 5))))

theorem res_PSU5 : ∀ r < 2048, r % 4 = 1 → ¬ (2 ^ 8 ∣ mPSU5 r ∧ ¬ 2 ^ 9 ∣ mPSU5 r) := by
  decide +kernel

theorem mPSU5_ne_zero {q : ℕ} (hq : 3 ≤ q) : mPSU5 q ≠ 0 := by
  have h2 : 1 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left hq 2
    omega
  have h4 : 1 ≤ q ^ 4 - 1 := by
    have := Nat.pow_le_pow_left hq 4
    omega
  unfold mPSU5
  positivity

theorem not_eight_PSU5 {q N : ℕ} (hq : q % 4 = 1) (hq3 : 3 ≤ q)
    (hN : N * Nat.gcd 5 (q + 1) = mPSU5 q) : N.factorization 2 ≠ 8 := by
  intro hf
  have hne := mPSU5_ne_zero hq3
  have hD : Nat.gcd 5 (q + 1) % 2 = 1 := by
    have hd : Nat.gcd 5 (q + 1) ∣ 5 := Nat.gcd_dvd_left _ _
    have : Odd (Nat.gcd 5 (q + 1)) := Odd.of_dvd_nat (by decide) hd
    exact Nat.odd_iff.mp this
  obtain ⟨h1, h2⟩ := residue_of_factorization_eight_odd mPSU5_congr (by omega) hD hN hne hf
  exact res_PSU5 (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h1, h2⟩

@[expose] def mRee (q : ℕ) : ℕ := q ^ 3 * ((q ^ 3 + 1) * (q - 1))

theorem mRee_congr (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD 2048]) :
    mRee a ≡ mRee b [MOD 2048] := by
  unfold mRee
  exact (h.pow 3).mul (((h.pow 3).add_right 1).mul (modEq_pred ha hb h))

theorem res_Ree : ∀ r < 2048, r % 8 = 3 → ¬ (2 ^ 8 ∣ mRee r ∧ ¬ 2 ^ 9 ∣ mRee r) := by
  decide +kernel

theorem not_eight_Ree {q N : ℕ} (hq : q % 8 = 3) (hN : N * 1 = mRee q) :
    N.factorization 2 ≠ 8 := by
  intro hf
  have hq3 : 3 ≤ q := by omega
  have hne : mRee q ≠ 0 := by
    have h1 : 1 ≤ q - 1 := by omega
    unfold mRee
    positivity
  obtain ⟨h1, h2⟩ := residue_of_factorization_eight_odd (D := 1) mRee_congr (by omega)
    (by norm_num) hN hne hf
  exact res_Ree (q % 2048) (Nat.mod_lt _ (by norm_num)) (by omega) ⟨h1, h2⟩

end CFSG.OddStandard.Solomon75
