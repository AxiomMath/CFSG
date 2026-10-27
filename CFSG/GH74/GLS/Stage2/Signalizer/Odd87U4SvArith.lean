module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvArith
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

section Ineq

theorem three_mul_succ_lt_five_pow {n : ℕ} (hn : 1 ≤ n) : 3 * n + 1 < 5 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ 5 n]; omega

theorem three_mul_add_two_lt_three_pow {n : ℕ} (hn : 2 ≤ n) : 3 * n + 2 < 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ 3 n]; omega

end Ineq

section Form

variable {p m : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem dvd_q_of_dvd_a_c (h1 : p ∣ 4 * m ^ 2 + 2 * m + 1) (h2 : p ∣ 2 * m ^ 2 + 2 * m + 1) :
    p ∣ 2 * m + 1 := by
  have h3 : p ∣ 2 * (2 * m ^ 2 + 2 * m + 1) := dvd_mul_of_dvd_right h2 _
  have e : 2 * (2 * m ^ 2 + 2 * m + 1) = (4 * m ^ 2 + 2 * m + 1) + (2 * m + 1) := by ring
  rw [e] at h3
  exact (Nat.dvd_add_right h1).1 h3

theorem su4_order_eq (m : ℕ) :
    (2 * m + 1) ^ 6 * ((2 * m + 1) ^ 2 - 1) * ((2 * m + 1) ^ 3 + 1) * ((2 * m + 1) ^ 4 - 1) =
      (2 * m + 1) ^ 6 *
        (64 * m ^ 2 * (m + 1) ^ 3 * (4 * m ^ 2 + 2 * m + 1) * (2 * m ^ 2 + 2 * m + 1)) := by
  have e1 : (2 * m + 1) ^ 2 - 1 = 4 * m * (m + 1) := by
    have : (2 * m + 1) ^ 2 = 4 * m * (m + 1) + 1 := by ring
    omega
  have e3 : (2 * m + 1) ^ 3 + 1 = 2 * (m + 1) * (4 * m ^ 2 + 2 * m + 1) := by ring
  have e4 : (2 * m + 1) ^ 4 - 1 = 8 * m * (m + 1) * (2 * m ^ 2 + 2 * m + 1) := by
    have : (2 * m + 1) ^ 4 = 8 * m * (m + 1) * (2 * m ^ 2 + 2 * m + 1) + 1 := by ring
    omega
  rw [e1, e3, e4]
  ring

theorem padicValNat_su4_form (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1) (hm : 1 ≤ m) :
    padicValNat p ((2 * m + 1) ^ 6 *
      (64 * m ^ 2 * (m + 1) ^ 3 * (4 * m ^ 2 + 2 * m + 1) * (2 * m ^ 2 + 2 * m + 1))) =
      2 * padicValNat p m + 3 * padicValNat p (m + 1) + padicValNat p (4 * m ^ 2 + 2 * m + 1) +
        padicValNat p (2 * m ^ 2 + 2 * m + 1) := by
  have h1 : (2 * m + 1) ^ 6 ≠ 0 := by positivity
  have h2 : 64 * m ^ 2 * (m + 1) ^ 3 * (4 * m ^ 2 + 2 * m + 1) * (2 * m ^ 2 + 2 * m + 1) ≠ 0 := by
    positivity
  rw [padicValNat.mul h1 h2, padicValNat.pow _ _, padicValNat.eq_zero_of_not_dvd hpq, mul_zero,
    zero_add, padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.eq_zero_of_not_dvd (not_dvd_sixtyfour hp2), padicValNat.pow _ _,
    padicValNat.pow _ _]
  ring

end Form

section Cases

theorem lt_of_cases_su4 {a b c d m p : ℕ} (hp5 : 5 ≤ p) (hm : 2 ≤ m) (hab : a = 0 ∨ b = 0)
    (hac : a = 0 ∨ c = 0) (had : a = 0 ∨ d = 0) (hbc : b = 0 ∨ c = 0) (hbd : b = 0 ∨ d = 0)
    (hcd : c = 0 ∨ d = 0) (ha : p ^ a ≤ m) (hb : p ^ b ≤ m + 1)
    (hc : c ≠ 0 → 7 ≤ p ∧ p ^ c ≤ 4 * m ^ 2 + 2 * m + 1) (hd : p ^ d ≤ 2 * m ^ 2 + 2 * m + 1) :
    2 * a + 3 * b + c + d < m := by
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
        have := sq_two_lt_seven_pow hm
        omega
    · have hc0 : c = 0 := hbc.resolve_left (by omega)
      have hd0 : d = 0 := hbd.resolve_left (by omega)
      subst hc0 hd0
      have h1 := three_mul_succ_lt_five_pow hb0
      have h2 : 5 ^ b ≤ p ^ b := Nat.pow_le_pow_left hp5 b
      omega
  · have hb0 : b = 0 := hab.resolve_left (by omega)
    have hc0 : c = 0 := hac.resolve_left (by omega)
    have hd0 : d = 0 := had.resolve_left (by omega)
    subst hb0 hc0 hd0
    have h1 := two_mul_succ_lt_five_pow ha0
    have h2 : 5 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp5 a
    omega

end Cases

section Main

variable {p m : ℕ} [Fact p.Prime]

theorem padicValNat_su4_lt (hm : 2 ≤ m) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 * m + 1)
    (hexc : ¬ (p = 3 ∧ m = 2)) :
    padicValNat p ((2 * m + 1) ^ 6 * ((2 * m + 1) ^ 2 - 1) * ((2 * m + 1) ^ 3 + 1) *
      ((2 * m + 1) ^ 4 - 1)) < m := by
  rw [su4_order_eq, padicValNat_su4_form hp2 hpq (by omega)]
  have ha : p ^ padicValNat p m ≤ m := pow_padicValNat_le (by omega)
  have hb : p ^ padicValNat p (m + 1) ≤ m + 1 := pow_padicValNat_le (by omega)
  have hc : p ^ padicValNat p (4 * m ^ 2 + 2 * m + 1) ≤ 4 * m ^ 2 + 2 * m + 1 :=
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
      have hc0 : padicValNat 3 (4 * m ^ 2 + 2 * m + 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        have e : 4 * m ^ 2 + 2 * m + 1 = 3 * (12 * k ^ 2 + 2 * k) + 1 := by rw [hk]; ring
        rw [e]; omega
      have ha1 : 1 ≤ padicValNat 3 m := one_le_padicValNat_of_dvd (by omega) ⟨k, hk⟩
      rw [hb0, hc0, hd3]
      have := two_mul_lt_three_pow ha1
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
      have hb1 : 1 ≤ padicValNat 3 (m + 1) := one_le_padicValNat_of_dvd (by omega) (by omega)
      have hm5 : 5 ≤ m := by
        have : m ≠ 2 := fun h => hexc ⟨rfl, h⟩
        omega
      rw [ha0, hc1, hd3]
      rcases Nat.lt_or_ge (padicValNat 3 (m + 1)) 2 with h1 | h1
      · omega
      · have := three_mul_add_two_lt_three_pow h1
        omega
  · have hp5 : 5 ≤ p := five_le_of_ne hp2 hp3
    refine lt_of_cases_su4 hp5 hm ?_ ?_ ?_ ?_ ?_ ?_ ha hb ?_ hd
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
      have h1 : 1 ≤ padicValNat p m := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact not_dvd_dvd_c_m (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      exact hp3 (eq_three_of_dvd_dvd_two (dvd_of_one_le_padicValNat h1)
        (dvd_of_one_le_padicValNat h2))
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact not_dvd_dvd_c_succ (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2)
    · by_contra hcon
      push Not at hcon
      have h1 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      have h2 : 1 ≤ padicValNat p (2 * m ^ 2 + 2 * m + 1) := by omega
      exact hpq (dvd_q_of_dvd_a_c (dvd_of_one_le_padicValNat h1) (dvd_of_one_le_padicValNat h2))
    · intro hc0
      have h2 : 1 ≤ padicValNat p (4 * m ^ 2 + 2 * m + 1) := by omega
      have hdv : p ∣ 4 * m ^ 2 + 2 * m + 1 := dvd_of_one_le_padicValNat h2
      exact ⟨seven_le_of_ne hp2 hp3 (ne_five_of_dvd_two hdv), hc⟩

end Main

section Numbers

variable {q p : ℕ} [Fact p.Prime]

theorem padicValNat_su4_order_lt (hq : Odd q) (hq5 : 5 ≤ q) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hexc : ¬ (q = 5 ∧ p = 3)) :
    padicValNat p (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) < (q - 1) / 2 := by
  obtain ⟨m, rfl⟩ := hq
  have hm2 : 2 ≤ m := by omega
  have e : (2 * m + 1 - 1) / 2 = m := by omega
  rw [e]
  exact padicValNat_su4_lt hm2 hp2 hpq (by
    rintro ⟨h3, h⟩
    exact hexc ⟨by omega, h3⟩)

theorem padicValNat_three_su4_five :
    padicValNat 3 (5 ^ 6 * (5 ^ 2 - 1) * (5 ^ 3 + 1) * (5 ^ 4 - 1)) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · by_contra h
    push Not at h
    have h3 : 3 ^ 5 ∣ 5 ^ 6 * (5 ^ 2 - 1) * (5 ^ 3 + 1) * (5 ^ 4 - 1) :=
      (padicValNat_dvd_iff_le (by norm_num)).2 (by omega)
    norm_num at h3
  · have h3 : 3 ^ 4 ∣ 5 ^ 6 * (5 ^ 2 - 1) * (5 ^ 3 + 1) * (5 ^ 4 - 1) := by norm_num
    exact (padicValNat_dvd_iff_le (by norm_num)).1 h3

theorem padicValNat_su4_three_le (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    padicValNat p (3 ^ 6 * (3 ^ 2 - 1) * (3 ^ 3 + 1) * (3 ^ 4 - 1)) ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hN : 3 ^ 6 * (3 ^ 2 - 1) * (3 ^ 3 + 1) * (3 ^ 4 - 1) = 13063680 := by norm_num
  rw [hN]
  by_contra h
  push Not at h
  have hsq : p ^ 2 ∣ 13063680 := (padicValNat_dvd_iff_le (by norm_num)).2 (by omega)
  have hpd : p ∣ 13063680 := (dvd_pow_self p two_ne_zero).trans hsq
  rcases prime_eq_five_or_seven hp hp2 hp3 hpd with rfl | rfl <;> norm_num at hsq

theorem padicValNat_su4_order_lt_sq (hq : Odd q) (hq3 : 3 ≤ q) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q) :
    padicValNat p (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) < (q ^ 2 - 1) / 2 := by
  rcases Nat.lt_or_ge q 5 with hq5 | hq5
  · obtain rfl : q = 3 := by
      obtain ⟨m, rfl⟩ := hq
      omega
    have hp3 : p ≠ 3 := fun h => hpq (by rw [h])
    have := padicValNat_su4_three_le hp2 hp3
    norm_num at this ⊢
    omega
  · by_cases hexc : q = 5 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := hexc
      rw [padicValNat_three_su4_five]
      norm_num
    · have h1 := padicValNat_su4_order_lt hq hq5 hp2 hpq hexc
      have h2 : (q - 1) / 2 ≤ (q ^ 2 - 1) / 2 :=
        Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.le_self_pow (by norm_num) q) 1)
      omega

end Numbers

section FieldLevel

variable {p₀ f₀ : ℕ} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem padicValNat_card_hypSU_lt (h : UnitaryFieldData p₀ f₀ K) (hodd : Odd (p₀ ^ f₀))
    (h5 : 5 ≤ p₀ ^ f₀) (hp2 : p ≠ 2) (hpq : ¬ p ∣ p₀ ^ f₀)
    (hexc : ¬ (p₀ ^ f₀ = 5 ∧ p = 3)) :
    padicValNat p (Nat.card ↥(hypSU h 2 0)) < (p₀ ^ f₀ - 1) / 2 := by
  rw [card_hypSU_four]
  exact padicValNat_su4_order_lt hodd h5 hp2 hpq hexc

theorem padicValNat_card_hypSU_lt_sq (h : UnitaryFieldData p₀ f₀ K) (hodd : Odd (p₀ ^ f₀))
    (h3 : 3 ≤ p₀ ^ f₀) (hp2 : p ≠ 2) (hpq : ¬ p ∣ p₀ ^ f₀) :
    padicValNat p (Nat.card ↥(hypSU h 2 0)) < ((p₀ ^ f₀) ^ 2 - 1) / 2 := by
  rw [card_hypSU_four]
  exact padicValNat_su4_order_lt_sq hodd h3 hp2 hpq

theorem padicValNat_three_card_hypSU_five (h : UnitaryFieldData p₀ f₀ K) (hq : p₀ ^ f₀ = 5) :
    padicValNat 3 (Nat.card ↥(hypSU h 2 0)) = 4 := by
  rw [card_hypSU_four, hq]
  exact padicValNat_three_su4_five

end FieldLevel

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
