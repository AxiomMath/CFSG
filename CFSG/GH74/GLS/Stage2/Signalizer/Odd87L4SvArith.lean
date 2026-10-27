module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvEngLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossArith

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open scoped MatrixGroups

section Ineq

theorem three_mul_lt_five_pow {n : ℕ} (hn : 1 ≤ n) : 3 * n < 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ 5 n]; omega

theorem three_mul_succ_lt_three_pow {n : ℕ} (hn : 2 ≤ n) : 3 * n + 1 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ 3 n]; omega

theorem sq_two_lt_five_pow {m : ℕ} (hm : 2 ≤ m) : 2 * m ^ 2 + 2 * m + 1 < 5 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 5 m]
    nlinarith

end Ineq

section Div

variable {p m : ℕ} [Fact p.Prime]

theorem not_dvd_sixtyfour (hp2 : p ≠ 2) : ¬ p ∣ 64 := fun h =>
  not_dvd_two hp2 ((Fact.out : p.Prime).dvd_of_dvd_pow (n := 6) (by simpa using h))

theorem not_dvd_dvd_c_m (h1 : p ∣ m) (h2 : p ∣ 2 * m ^ 2 + 2 * m + 1) : False := by
  have : 2 * m ^ 2 + 2 * m + 1 = m * (2 * m + 2) + 1 := by ring
  rw [this] at h2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1
    ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2))

theorem not_dvd_dvd_c_succ (h1 : p ∣ m + 1) (h2 : p ∣ 2 * m ^ 2 + 2 * m + 1) : False := by
  have : 2 * m ^ 2 + 2 * m + 1 = (m + 1) * (2 * m) + 1 := by ring
  rw [this] at h2
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1
    ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).1 h2))

omit [Fact p.Prime] in
theorem dvd_q_of_dvd_b_c (h1 : p ∣ 4 * m ^ 2 + 6 * m + 3) (h2 : p ∣ 2 * m ^ 2 + 2 * m + 1) :
    p ∣ 2 * m + 1 := by
  have : 4 * m ^ 2 + 6 * m + 3 = 2 * (2 * m ^ 2 + 2 * m + 1) + (2 * m + 1) := by ring
  rw [this] at h1
  exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h2 _)).1 h1

theorem not_three_dvd_c (m : ℕ) : ¬ 3 ∣ 2 * m ^ 2 + 2 * m + 1 := by
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k := ⟨m / 3, by omega⟩
    have : 2 * (3 * k) ^ 2 + 2 * (3 * k) + 1 = 3 * (6 * k ^ 2 + 2 * k) + 1 := by ring
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 1 := ⟨m / 3, by omega⟩
    have : 2 * (3 * k + 1) ^ 2 + 2 * (3 * k + 1) + 1 = 3 * (6 * k ^ 2 + 6 * k + 1) + 2 := by ring
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
    have : 2 * (3 * k + 2) ^ 2 + 2 * (3 * k + 2) + 1 = 3 * (6 * k ^ 2 + 10 * k + 4) + 1 := by ring
    omega

end Div


section Form

variable {p m : ℕ} [Fact p.Prime]

theorem sl4_order_eq (m : ℕ) :
    (2 * m + 1) ^ 6 * ((2 * m + 1) ^ 2 - 1) * ((2 * m + 1) ^ 3 - 1) * ((2 * m + 1) ^ 4 - 1) =
      (2 * m + 1) ^ 6 *
        (64 * m ^ 3 * (m + 1) ^ 2 * (4 * m ^ 2 + 6 * m + 3) * (2 * m ^ 2 + 2 * m + 1)) := by
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) := by
    have : (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 := by ring
    omega
  have e2 : (2 * m + 1) ^ 3 - 1 = 2 * m * (4 * m ^ 2 + 6 * m + 3) := by
    have : (2 * m + 1) ^ 3 = 2 * m * (4 * m ^ 2 + 6 * m + 3) + 1 := by ring
    omega
  have e4 : (2 * m + 1) ^ 4 - 1 = 8 * m * (m + 1) * (2 * m ^ 2 + 2 * m + 1) := by
    have : (2 * m + 1) ^ 4 = 8 * m * (m + 1) * (2 * m ^ 2 + 2 * m + 1) + 1 := by ring
    omega
  rw [e1, e2, e4]
  ring

theorem padicValNat_sl4_form (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) (hm : 1 ≤ m) :
    padicValNat p ((2 * m + 1) ^ 6 *
      (64 * m ^ 3 * (m + 1) ^ 2 * (4 * m ^ 2 + 6 * m + 3) * (2 * m ^ 2 + 2 * m + 1))) =
      3 * padicValNat p m + 2 * padicValNat p (m + 1) + padicValNat p (4 * m ^ 2 + 6 * m + 3) +
        padicValNat p (2 * m ^ 2 + 2 * m + 1) := by
  have h1 : (2 * m + 1) ^ 6 ≠ 0 := by positivity
  have h2 : 64 * m ^ 3 * (m + 1) ^ 2 * (4 * m ^ 2 + 6 * m + 3) * (2 * m ^ 2 + 2 * m + 1) ≠ 0 := by
    positivity
  rw [padicValNat.mul h1 h2, padicValNat.pow _ _, padicValNat.eq_zero_of_not_dvd hpq, mul_zero,
    zero_add, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.eq_zero_of_not_dvd (not_dvd_sixtyfour hp2), padicValNat.pow _ _, padicValNat.pow _ _]
  ring

end Form

section Cases

theorem lt_of_cases_sl4 {a b c d m p : ℕ} (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hab : a = 0 ∨ b = 0)
    (hac : a = 0 ∨ c = 0) (had : a = 0 ∨ d = 0) (hbc : b = 0 ∨ c = 0) (hbd : b = 0 ∨ d = 0)
    (hcd : c = 0 ∨ d = 0) (ha : p ^ a ≤ m) (hb : p ^ b ≤ m + 1)
    (hc : c ≠ 0 → 7 ≤ p ∧ p ^ c ≤ 4 * m ^ 2 + 6 * m + 3) (hd : p ^ d ≤ 2 * m ^ 2 + 2 * m + 1) :
    3 * a + 2 * b + c + d < m := by
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      rcases Nat.eq_zero_or_pos c with hc0 | hc0
      · subst hc0
        rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0; omega
        · by_contra hlt
          have h1 : 5 ^ m ≤ 5 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : 5 ^ d ≤ p ^ d := Nat.pow_le_pow_left hp5 d
          have := sq_two_lt_five_pow hm
          omega
      · have hd0 : d = 0 := hcd.resolve_left (by omega)
        subst hd0
        obtain ⟨h7, hpc⟩ := hc (by omega)
        by_contra hlt
        have h1 : 7 ^ m ≤ 7 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : 7 ^ c ≤ p ^ c := Nat.pow_le_pow_left h7 c
        have := sq_six_lt_seven_pow hm
        omega
    · have hc0 : c = 0 := hbc.resolve_left (by omega)
      have hd0 : d = 0 := hbd.resolve_left (by omega)
      subst hc0 hd0
      have h1 := two_mul_succ_lt_five_pow hb0
      have h2 : 5 ^ b ≤ p ^ b := Nat.pow_le_pow_left hp5 b
      omega
  · have hb0 : b = 0 := hab.resolve_left (by omega)
    have hc0 : c = 0 := hac.resolve_left (by omega)
    have hd0 : d = 0 := had.resolve_left (by omega)
    subst hb0 hc0 hd0
    have h1 := three_mul_lt_five_pow ha0
    have h2 : 5 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp5 a
    omega

end Cases


section Main

variable {p m : ℕ} [Fact p.Prime]

theorem padicValNat_sl4_lt (hm : 2 ≤ m) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1)
    (hexc : ¬ (p = 3 ∧ (m = 2 ∨ m = 3))) :
    padicValNat p ((2 * m + 1) ^ 6 * ((2 * m + 1) ^ 2 - 1) * ((2 * m + 1) ^ 3 - 1) *
      ((2 * m + 1) ^ 4 - 1)) < m := by
  rw [sl4_order_eq, padicValNat_sl4_form hp2 hpq (by omega)]
  have ha : p ^ padicValNat p m ≤ m := pow_padicValNat_le (by omega)
  have hb : p ^ padicValNat p (m + 1) ≤ m + 1 := pow_padicValNat_le (by omega)
  have hc : p ^ padicValNat p (4 * m ^ 2 + 6 * m + 3) ≤ 4 * m ^ 2 + 6 * m + 3 :=
    pow_padicValNat_le (by positivity)
  have hd : p ^ padicValNat p (2 * m ^ 2 + 2 * m + 1) ≤ 2 * m ^ 2 + 2 * m + 1 :=
    pow_padicValNat_le (by positivity)
  by_cases hp3 : p = 3
  · subst hp3
    have hd3 : padicValNat 3 (2 * m ^ 2 + 2 * m + 1) = 0 :=
      padicValNat.eq_zero_of_not_dvd (not_three_dvd_c m)
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
      have ha1 : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd (by omega) ⟨k, hk⟩
      have hm6 : 6 ≤ m := by
        have : m ≠ 3 := fun h => hexc ⟨rfl, Or.inr h⟩
        omega
      rw [hb0, hc1, hd3]
      rcases Nat.lt_or_ge (padicValNat 3 m) 2 with h1 | h1
      · omega
      · have := three_mul_succ_lt_three_pow h1
        omega
    · have ha0 : padicValNat 3 m = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
      have hc0 : padicValNat 3 (4 * m ^ 2 + 6 * m + 3) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        obtain ⟨k, hk⟩ : ∃ k, m = 3 * k + 2 := ⟨m / 3, by omega⟩
        have e : 4 * m ^ 2 + 6 * m + 3 = 3 * (12 * k ^ 2 + 22 * k + 10) + 1 := by rw [hk]; ring
        rw [e]; omega
      have hb1 : 1 ≤ padicValNat 3 (m + 1) := one_le_padicValNat_of_dvd (by omega) (by omega)
      have hm5 : 5 ≤ m := by
        have : m ≠ 2 := fun h => hexc ⟨rfl, Or.inl h⟩
        omega
      rw [ha0, hc0, hd3]
      rcases Nat.lt_or_ge (padicValNat 3 (m + 1)) 2 with h1 | h1
      · omega
      · have := two_mul_succ_lt_three_pow h1
        omega
  · have hp5 : 5 ≤ p := five_le_of_ne hp2 hp3
    refine lt_of_cases_sl4 hp5 hm ?_ ?_ ?_ ?_ ?_ ?_ ha hb ?_ hd
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
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact not_dvd_dvd_c_m (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      exact not_dvd_dvd_six (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact not_dvd_dvd_c_succ (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact hpq (dvd_q_of_dvd_b_c (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2))
    · intro hc0
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 6 * m + 3) := by omega
      have hdv : p ∣ 4 * m ^ 2 + 6 * m + 3 := dvd_of_one_le_padicValNat h2
      exact ⟨seven_le_of_ne hp2 hp3 (ne_five_of_dvd_six hdv), hc⟩

end Main


section FieldLevel

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem padicValNat_card_sl4_lt (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ Nat.card F) (hexc : ¬ (p = 3 ∧ (Nat.card F = 5 ∨ Nat.card F = 7))) :
    padicValNat p (Nat.card SL(4, F)) < (Nat.card F - 1) / 2 := by
  obtain ⟨m, hm⟩ := hodd
  rw [card_specialLinear_four, hm]
  rw [hm] at hpq h5 hexc
  have hm2 : 2 ≤ m := by omega
  have e : (2 * m + 1 - 1) / 2 = m := by omega
  rw [e]
  exact padicValNat_sl4_lt hm2 hp2 hpq (by
    rintro ⟨h3, h⟩
    exact hexc ⟨h3, by omega⟩)

omit [Fact p.Prime] in
theorem padicValNat_three_card_sl4_five (hF : Nat.card F = 5) :
    padicValNat 3 (Nat.card SL(4, F)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_specialLinear_four, hF]
  by_contra h
  push Not at h
  have h3 : 3 ^ 3 ∣ 5 ^ 6 * (5 ^ 2 - 1) * (5 ^ 3 - 1) * (5 ^ 4 - 1) :=
    (padicValNat_dvd_iff_le (by norm_num)).2 (by omega)
  norm_num at h3

omit [Fact p.Prime] in
theorem padicValNat_three_card_sl4_seven (hF : Nat.card F = 7) :
    padicValNat 3 (Nat.card SL(4, F)) ≤ 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [card_specialLinear_four, hF]
  by_contra h
  push Not at h
  have h3 : 3 ^ 5 ∣ 7 ^ 6 * (7 ^ 2 - 1) * (7 ^ 3 - 1) * (7 ^ 4 - 1) :=
    (padicValNat_dvd_iff_le (by norm_num)).2 (by omega)
  norm_num at h3

end FieldLevel

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
