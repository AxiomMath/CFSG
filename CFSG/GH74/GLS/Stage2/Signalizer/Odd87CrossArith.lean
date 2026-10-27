module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

@[expose] def psl3Order (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) / Nat.gcd 3 (q - 1)

@[expose] def psu3Order (q : ℕ) : ℕ := q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) / Nat.gcd 3 (q + 1)

section Ineq

theorem two_mul_lt_three_pow {n : ℕ} (hn : 1 ≤ n) : 2 * n < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ _ n]; omega

theorem two_mul_succ_lt_five_pow {n : ℕ} (hn : 1 ≤ n) : 2 * n + 1 < 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ _ n]; omega

theorem two_mul_succ_lt_three_pow {n : ℕ} (hn : 2 ≤ n) : 2 * n + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ _ n]; omega

theorem sq_six_lt_seven_pow {m : ℕ} (hm : 2 ≤ m) : 4 * m ^ 2 + 6 * m + 3 < 7 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 7 m]
    nlinarith

theorem sq_two_lt_seven_pow {m : ℕ} (hm : 2 ≤ m) : 4 * m ^ 2 + 2 * m + 1 < 7 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 7 m]
    nlinarith

end Ineq

section Val

variable {p m : ℕ} [Fact p.Prime]

theorem not_dvd_two (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h)

theorem not_dvd_eight (hp2 : p ≠ 2) : ¬ p ∣ 8 := fun h =>
  not_dvd_two hp2 ((Fact.out : p.Prime).dvd_of_dvd_pow (n := 3) (by simpa using h))

theorem padicValNat_sl3_form (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) (hm : 1 ≤ m) :
    padicValNat p ((2 * m + 1) ^ 3 * (8 * m ^ 2 * (m + 1) * (4 * m ^ 2 + 6 * m + 3))) =
      2 * padicValNat p m + padicValNat p (m + 1) + padicValNat p (4 * m ^ 2 + 6 * m + 3) := by
  have h1 : (2 * m + 1) ^ 3 ≠ 0 := by positivity
  have h2 : 8 * m ^ 2 * (m + 1) * (4 * m ^ 2 + 6 * m + 3) ≠ 0 := by positivity
  rw [padicValNat.mul h1 h2, padicValNat.pow _ _,
    padicValNat.eq_zero_of_not_dvd hpq, mul_zero, zero_add,
    padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.eq_zero_of_not_dvd (not_dvd_eight hp2),
    padicValNat.pow _ _]
  ring

theorem padicValNat_su3_form (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) (hm : 1 ≤ m) :
    padicValNat p ((2 * m + 1) ^ 3 * (8 * m * (m + 1) ^ 2 * (4 * m ^ 2 + 2 * m + 1))) =
      padicValNat p m + 2 * padicValNat p (m + 1) + padicValNat p (4 * m ^ 2 + 2 * m + 1) := by
  have h1 : (2 * m + 1) ^ 3 ≠ 0 := by positivity
  have h2 : 8 * m * (m + 1) ^ 2 * (4 * m ^ 2 + 2 * m + 1) ≠ 0 := by positivity
  rw [padicValNat.mul h1 h2, padicValNat.pow _ _,
    padicValNat.eq_zero_of_not_dvd hpq, mul_zero, zero_add,
    padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.eq_zero_of_not_dvd (not_dvd_eight hp2),
    padicValNat.pow _ _]
  ring

end Val

section Div

variable {p m : ℕ} [Fact p.Prime]

theorem not_dvd_both_succ (h1 : p ∣ m) (h2 : p ∣ m + 1) : False :=
  (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h1).1 h2))

theorem eq_three_of_dvd_three (h : p ∣ 3) : p = 3 :=
  (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).1 h

theorem eq_three_of_dvd_dvd_six (h1 : p ∣ m) (h2 : p ∣ 4 * m ^ 2 + 6 * m + 3) : p = 3 := by
  have : 4 * m ^ 2 + 6 * m + 3 = m * (4 * m + 6) + 3 := by ring
  rw [this] at h2
  exact eq_three_of_dvd_three ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2)

theorem not_dvd_dvd_six (h1 : p ∣ m + 1) (h2 : p ∣ 4 * m ^ 2 + 6 * m + 3) : False := by
  have : 4 * m ^ 2 + 6 * m + 3 = (m + 1) * (4 * m + 2) + 1 := by ring
  rw [this] at h2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1
    ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2))

theorem not_dvd_dvd_two (h1 : p ∣ m) (h2 : p ∣ 4 * m ^ 2 + 2 * m + 1) : False := by
  have : 4 * m ^ 2 + 2 * m + 1 = m * (4 * m + 2) + 1 := by ring
  rw [this] at h2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1
    ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2))

theorem eq_three_of_dvd_dvd_two (h1 : p ∣ m + 1) (h2 : p ∣ 4 * m ^ 2 + 2 * m + 1) : p = 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := by
    rcases m with _ | n
    · exact absurd (Nat.dvd_one.1 h1) (Fact.out : p.Prime).one_lt.ne'
    · exact ⟨n, rfl⟩
  have : 4 * (n + 1) ^ 2 + 2 * (n + 1) + 1 = (n + 1 + 1) * (4 * n + 2) + 3 := by ring
  rw [this] at h2
  exact eq_three_of_dvd_three ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2)

theorem ne_five_of_dvd_six (h : p ∣ 4 * m ^ 2 + 6 * m + 3) : p ≠ 5 := by
  rintro rfl
  have h5 : (4 * m ^ 2 + 6 * m + 3) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  have h6 : (4 * m ^ 2 + 6 * m + 3) % 5 = (4 * (m % 5) ^ 2 + 6 * (m % 5) + 3) % 5 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [h6] at h5
  have hm5 : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize m % 5 = r at h5 hm5
  interval_cases r <;> simp at h5

theorem ne_five_of_dvd_two (h : p ∣ 4 * m ^ 2 + 2 * m + 1) : p ≠ 5 := by
  rintro rfl
  have h5 : (4 * m ^ 2 + 2 * m + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  have h6 : (4 * m ^ 2 + 2 * m + 1) % 5 = (4 * (m % 5) ^ 2 + 2 * (m % 5) + 1) % 5 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  rw [h6] at h5
  have hm5 : m % 5 < 5 := Nat.mod_lt _ (by norm_num)
  generalize m % 5 = r at h5 hm5
  interval_cases r <;> simp at h5

theorem seven_le_of_ne (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) : 7 ≤ p := by
  have h2 := (Fact.out : p.Prime).two_le
  by_contra hlt
  have : p ≤ 6 := by omega
  interval_cases p <;> first | omega | exact absurd (Fact.out : Nat.Prime 4) (by decide) |
    exact absurd (Fact.out : Nat.Prime 6) (by decide)

end Div

section Cases

theorem lt_of_cases_A {a b c m p : ℕ} (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hab : a = 0 ∨ b = 0)
    (hac : a = 0 ∨ c = 0) (hbc : b = 0 ∨ c = 0) (ha : p ^ a ≤ m) (hb : p ^ b ≤ m + 1)
    (hc : c ≠ 0 → 7 ≤ p ∧ p ^ c ≤ 4 * m ^ 2 + 6 * m + 3) : 2 * a + b + c < m := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      by_cases hc0 : c = 0
      · subst hc0; omega
      · obtain ⟨h7, hpc⟩ := hc hc0
        by_contra hlt
        have h1 : 7 ^ m ≤ 7 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 7 ^ c ≤ p ^ c := Nat.pow_le_pow_left h7 c
        have := sq_six_lt_seven_pow hm
        omega
    · have hc0 : c = 0 := hbc.resolve_left (by omega)
      subst hc0
      have h1 := two_mul_lt_three_pow hb0
      have h2 : 3 ^ b ≤ p ^ b := Nat.pow_le_pow_left (by omega) b
      omega
  · have hb0 : b = 0 := hab.resolve_left (by omega)
    have hc0 : c = 0 := hac.resolve_left (by omega)
    subst hb0 hc0
    have h1 := two_mul_succ_lt_five_pow ha0
    have h2 : 5 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp5 a
    omega

theorem lt_of_cases_B {a b c m p : ℕ} (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hab : a = 0 ∨ b = 0)
    (hac : a = 0 ∨ c = 0) (hbc : b = 0 ∨ c = 0) (ha : p ^ a ≤ m) (hb : p ^ b ≤ m + 1)
    (hc : c ≠ 0 → 7 ≤ p ∧ p ^ c ≤ 4 * m ^ 2 + 2 * m + 1) : a + 2 * b + c < m := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      by_cases hc0 : c = 0
      · subst hc0; omega
      · obtain ⟨h7, hpc⟩ := hc hc0
        by_contra hlt
        have h1 : 7 ^ m ≤ 7 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 7 ^ c ≤ p ^ c := Nat.pow_le_pow_left h7 c
        have := sq_two_lt_seven_pow hm
        omega
    · have hc0 : c = 0 := hbc.resolve_left (by omega)
      subst hc0
      have h1 := two_mul_succ_lt_five_pow hb0
      have h2 : 5 ^ b ≤ p ^ b := Nat.pow_le_pow_left hp5 b
      omega
  · have hb0 : b = 0 := hab.resolve_left (by omega)
    have hc0 : c = 0 := hac.resolve_left (by omega)
    subst hb0 hc0
    have h1 : a < p ^ a := Nat.lt_pow_self (by omega)
    omega

end Cases

section Orders

theorem psl3Order_eq (m : ℕ) : psl3Order (2 * m + 1) =
    (2 * m + 1) ^ 3 * (8 * m ^ 2 * (m + 1) * (4 * m ^ 2 + 6 * m + 3)) / Nat.gcd 3 (2 * m) := by
  unfold psl3Order
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) := by
    have : (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 := by ring
    omega
  have e2 : (2 * m + 1) ^ 3 - 1 = 2 * m * (4 * m ^ 2 + 6 * m + 3) := by
    have : (2 * m + 1) ^ 3 = 2 * m * (4 * m ^ 2 + 6 * m + 3) + 1 := by ring
    omega
  have e3 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [e1, e2, e3]
  congr 1
  ring

theorem psu3Order_eq (m : ℕ) : psu3Order (2 * m + 1) =
    (2 * m + 1) ^ 3 * (8 * m * (m + 1) ^ 2 * (4 * m ^ 2 + 2 * m + 1)) / Nat.gcd 3 (2 * m + 2) := by
  unfold psu3Order
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) := by
    have : (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 := by ring
    omega
  have e2 : (2 * m + 1) ^ 3 + 1 = (2 * m + 2) * (4 * m ^ 2 + 2 * m + 1) := by ring
  have e3 : 2 * m + 1 + 1 = 2 * m + 2 := by omega
  rw [e1, e2, e3]
  congr 1
  ring

end Orders

section Main

variable {p m : ℕ} [Fact p.Prime]

theorem five_le_of_ne (hp2 : p ≠ 2) (hp3 : p ≠ 3) : 5 ≤ p := by
  have h2 := (Fact.out : p.Prime).two_le
  by_contra hlt
  have : p ≤ 4 := by omega
  interval_cases p <;> first | omega | exact absurd (Fact.out : Nat.Prime 4) (by decide)

omit [Fact p.Prime] in
theorem pow_padicValNat_le {n : ℕ} (hn : 0 < n) : p ^ padicValNat p n ≤ n :=
  Nat.le_of_dvd hn pow_padicValNat_dvd

theorem padicValNat_gcd_three_of_ne (hp3 : p ≠ 3) (n : ℕ) : padicValNat p (Nat.gcd 3 n) = 0 :=
  padicValNat.eq_zero_of_not_dvd fun h =>
    hp3 (eq_three_of_dvd_three (h.trans (Nat.gcd_dvd_left 3 n)))

theorem padicValNat_psl3_lt (hm : 2 ≤ m) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) :
    padicValNat p (psl3Order (2 * m + 1)) < m := by
  have hdvd : Nat.gcd 3 (2 * m) ∣
      (2 * m + 1) ^ 3 * (8 * m ^ 2 * (m + 1) * (4 * m ^ 2 + 6 * m + 3)) :=
    (Nat.gcd_dvd_right 3 (2 * m)).trans
      ⟨(2 * m + 1) ^ 3 * (4 * m * (m + 1) * (4 * m ^ 2 + 6 * m + 3)), by ring⟩
  rw [psl3Order_eq, padicValNat.div_of_dvd hdvd, padicValNat_sl3_form hp2 hpq (by omega)]
  have ha : p ^ padicValNat p m ≤ m := pow_padicValNat_le (by omega)
  have hb : p ^ padicValNat p (m + 1) ≤ m + 1 := pow_padicValNat_le (by omega)
  have hc : p ^ padicValNat p (4 * m ^ 2 + 6 * m + 3) ≤ 4 * m ^ 2 + 6 * m + 3 :=
    pow_padicValNat_le (by positivity)
  by_cases hp3 : p = 3
  · subst hp3
    have hm3 : m % 3 = 0 ∨ m % 3 = 2 := by
      rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
      · exact Or.inl h
      · exact absurd (by omega : 3 ∣ 2 * m + 1) hpq
      · exact Or.inr h
    rcases hm3 with h0 | h2
    · obtain ⟨k, hk⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
      have hb0 : padicValNat 3 (m + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hc1 : padicValNat 3 (4 * m ^ 2 + 6 * m + 3) = 1 := by
        have e : 4 * m ^ 2 + 6 * m + 3 = 3 * (12 * k ^ 2 + 6 * k + 1) := by rw [hk]; ring
        have hn : ¬ 3 ∣ 12 * k ^ 2 + 6 * k + 1 := by
          obtain ⟨t, ht⟩ : ∃ t, 12 * k ^ 2 + 6 * k + 1 = 3 * t + 1 := ⟨4 * k ^ 2 + 2 * k, by ring⟩
          rw [ht]; omega
        rw [e, padicValNat.mul (by norm_num) (by positivity), padicValNat_self,
          padicValNat.eq_zero_of_not_dvd hn]
      have hg : padicValNat 3 (Nat.gcd 3 (2 * m)) = 1 := by
        rw [Nat.gcd_eq_left (⟨2 * k, by rw [hk]; ring⟩ : 3 ∣ 2 * m), padicValNat_self]
      have ha1 : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd (by omega) ⟨k, hk⟩
      have := two_mul_lt_three_pow ha1
      rw [hb0, hc1, hg]
      omega
    · have ha0 : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hc0 : padicValNat 3 (4 * m ^ 2 + 6 * m + 3) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
        have e : 4 * m ^ 2 + 6 * m + 3 = 3 * (12 * k ^ 2 + 22 * k + 10) + 1 := by rw [hk]; ring
        rw [e]; omega
      have hg : padicValNat 3 (Nat.gcd 3 (2 * m)) = 0 := by
        rw [(Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
          (by omega))), padicValNat_one_right]
      have hb1 : 1 ≤ padicValNat 3 (m + 1) := one_le_padicValNat_of_dvd (by omega) (by omega)
      have := two_mul_lt_three_pow hb1
      rw [ha0, hc0, hg]
      omega
  · have hg : padicValNat p (Nat.gcd 3 (2 * m)) = 0 := padicValNat_gcd_three_of_ne hp3 _
    rw [hg, Nat.sub_zero]
    have hp5 : 5 ≤ p := five_le_of_ne hp2 hp3
    refine lt_of_cases_A hp5 hm ?_ ?_ ?_ ha hb ?_
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (m + 1) := by omega
      exact not_dvd_both_succ (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      exact hp3 (eq_three_of_dvd_dvd_six (dvd_of_one_le_padicValNat h1)
        (dvd_of_one_le_padicValNat h2))
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      exact not_dvd_dvd_six (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · intro hc0
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      have hd : p ∣ 4 * m ^ 2 + 6 * m + 3 := dvd_of_one_le_padicValNat h2
      exact ⟨seven_le_of_ne hp2 hp3 (ne_five_of_dvd_six hd), hc⟩

end Main

section MainU

variable {p m : ℕ} [Fact p.Prime]

theorem padicValNat_psu3_lt (hm : 2 ≤ m) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) :
    padicValNat p (psu3Order (2 * m + 1)) < m ∨ (m = 2 ∧ p = 3) := by
  have hdvd : Nat.gcd 3 (2 * m + 2) ∣
      (2 * m + 1) ^ 3 * (8 * m * (m + 1) ^ 2 * (4 * m ^ 2 + 2 * m + 1)) :=
    (Nat.gcd_dvd_right 3 (2 * m + 2)).trans
      ⟨(2 * m + 1) ^ 3 * (4 * m * (m + 1) * (4 * m ^ 2 + 2 * m + 1)), by ring⟩
  rw [psu3Order_eq, padicValNat.div_of_dvd hdvd, padicValNat_su3_form hp2 hpq (by omega)]
  have ha : p ^ padicValNat p m ≤ m := pow_padicValNat_le (by omega)
  have hb : p ^ padicValNat p (m + 1) ≤ m + 1 := pow_padicValNat_le (by omega)
  have hc : p ^ padicValNat p (4 * m ^ 2 + 2 * m + 1) ≤ 4 * m ^ 2 + 2 * m + 1 :=
    pow_padicValNat_le (by positivity)
  by_cases hp3 : p = 3
  · subst hp3
    have hm3 : m % 3 = 0 ∨ m % 3 = 2 := by
      rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
      · exact Or.inl h
      · exact absurd (by omega : 3 ∣ 2 * m + 1) hpq
      · exact Or.inr h
    rcases hm3 with h0 | h2
    · left
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
      have hb0 : padicValNat 3 (m + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hc0 : padicValNat 3 (4 * m ^ 2 + 2 * m + 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        have e : 4 * m ^ 2 + 2 * m + 1 = 3 * (12 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
        rw [e]; omega
      have hg : padicValNat 3 (Nat.gcd 3 (2 * m + 2)) = 0 := by
        rw [(Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
          (by omega))), padicValNat_one_right]
      have ha1 : padicValNat 3 m < 3 ^ padicValNat 3 m := Nat.lt_pow_self (by norm_num)
      rw [hb0, hc0, hg]
      omega
    · have ha0 : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
      have hc1 : padicValNat 3 (4 * m ^ 2 + 2 * m + 1) = 1 := by
        have e : 4 * m ^ 2 + 2 * m + 1 = 3 * (12 * k ^ 2 + 18 * k + 7) := by rw [hk]; ring
        have hn : ¬ 3 ∣ 12 * k ^ 2 + 18 * k + 7 := by
          obtain ⟨t, ht⟩ : ∃ t, 12 * k ^ 2 + 18 * k + 7 = 3 * t + 1 :=
            ⟨4 * k ^ 2 + 6 * k + 2, by ring⟩
          rw [ht]; omega
        rw [e, padicValNat.mul (by norm_num) (by positivity), padicValNat_self,
          padicValNat.eq_zero_of_not_dvd hn]
      have hg : padicValNat 3 (Nat.gcd 3 (2 * m + 2)) = 1 := by
        rw [Nat.gcd_eq_left (⟨2 * k + 2, by rw [hk]; ring⟩ : 3 ∣ 2 * m + 2), padicValNat_self]
      have hb1 : 1 ≤ padicValNat 3 (m + 1) := one_le_padicValNat_of_dvd (by omega) (by omega)
      rw [ha0, hc1, hg]
      by_cases hb2 : 2 ≤ padicValNat 3 (m + 1)
      · left
        have := two_mul_succ_lt_three_pow hb2
        omega
      · have hb1' : padicValNat 3 (m + 1) = 1 := by omega
        rw [hb1'] at hb ⊢
        by_cases hm2 : m = 2
        · right
          exact ⟨hm2, rfl⟩
        · left
          omega
  · left
    have hg : padicValNat p (Nat.gcd 3 (2 * m + 2)) = 0 := padicValNat_gcd_three_of_ne hp3 _
    rw [hg, Nat.sub_zero]
    have hp5 : 5 ≤ p := five_le_of_ne hp2 hp3
    refine lt_of_cases_B hp5 hm ?_ ?_ ?_ ha hb ?_
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (m + 1) := by omega
      exact not_dvd_both_succ (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      exact not_dvd_dvd_two (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      exact hp3 (eq_three_of_dvd_dvd_two (dvd_of_one_le_padicValNat h1)
        (dvd_of_one_le_padicValNat h2))
    · intro hc0
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      have hd : p ∣ 4 * m ^ 2 + 2 * m + 1 := dvd_of_one_le_padicValNat h2
      exact ⟨seven_le_of_ne hp2 hp3 (ne_five_of_dvd_two hd), hc⟩

end MainU

section Final

theorem psl3Order_eq_linearModel (q : ℕ) :
    psl3Order q = q ^ (3 * (3 - 1) / 2) * (∏ j ∈ Finset.Icc 2 3, (q ^ j - 1)) / Nat.gcd 3 (q - 1) := by
  unfold psl3Order
  have h : Finset.Icc 2 3 = {2, 3} := by decide
  rw [h, Finset.prod_pair (by norm_num)]
  norm_num [mul_assoc]

theorem padicValNat_psl3Order_lt {q p : ℕ} [Fact p.Prime] (hq : Odd q) (hq5 : 5 ≤ q)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) : padicValNat p (psl3Order q) < (q - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hq
  have h := padicValNat_psl3_lt (p := p) (m := m) (by omega) hp2 hpq
  have e : (2 * m + 1 - 1) / 2 = m := by omega
  rw [e]
  exact h

theorem padicValNat_psu3Order_lt {q p : ℕ} [Fact p.Prime] (hq : Odd q) (hq5 : 5 ≤ q)
    (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) :
    padicValNat p (psu3Order q) < (q - 1) / 2 ∨ (q = 5 ∧ p = 3) := by
  obtain ⟨m, rfl⟩ := hq
  have e : (2 * m + 1 - 1) / 2 = m := by omega
  rcases padicValNat_psu3_lt (p := p) (m := m) (by omega) hp2 hpq with h | ⟨hm, hp⟩
  · exact Or.inl (by rw [e]; exact h)
  · exact Or.inr ⟨by omega, hp⟩

theorem padicValNat_psu3Order_five_three : padicValNat 3 (psu3Order 5) = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : psu3Order 5 = 3 ^ 2 * 14000 := by decide
  rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end Final

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
