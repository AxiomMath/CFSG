module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem numerics_pow_ge {p r : ℕ} (hp : 3 ≤ p) (hr : 2 ≤ r) : r + 6 ≤ p ^ r := by
  have h3 : r + 6 ≤ 3 ^ r := by
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  exact h3.trans (Nat.pow_le_pow_left hp r)

theorem numerics_r_eq_one {p r a c mZ w z m D : ℕ} (hp : 3 ≤ p) (hr : 1 ≤ r)
    (master : mZ + w + (p ^ r - 1) * m ≤ r + a + c + p ^ r * z)
    (haD : a ≤ D) (T1a : D ≤ m + 2) (T2 : 2 * z ≤ m) (hm : 1 ≤ m) (hzw : z ≤ w)
    (hcZ : c ≤ mZ) : r = 1 := by
  by_contra hne
  have hr2 : 2 ≤ r := by omega
  have hP := numerics_pow_ge hp hr2
  generalize p ^ r = P at master hP
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, m = z + u := ⟨m - z, by omega⟩
  have hu : 1 ≤ u := by omega
  have hQu : Q ≤ Q * u := Nat.le_mul_of_pos_right Q hu
  simp only [Nat.add_sub_cancel] at master
  nlinarith

theorem numerics_dichotomy {p r a c mZ w z m D zOrd : ℕ} (hp : 3 ≤ p) (hp4 : p ≠ 4) (hr : 1 ≤ r)
    (master : mZ + w + (p ^ r - 1) * m ≤ r + a + c + p ^ r * z)
    (haD : a ≤ D) (T1a : D ≤ m + 2) (T1b : (m < 7 ∨ p ∣ zOrd) → D ≤ m + 1)
    (T2 : 2 * z ≤ m) (hm : 1 ≤ m) (hzw : z ≤ w)
    (hzp : zOrd = 1 ∨ p ∣ zOrd) (hz0 : z = 0 ↔ zOrd = 1)
    (T3 : z = 1 → ((p = 3 ∧ zOrd = 3) ∨ p + 2 ≤ (p - 2) * m))
    (T11 : 2 ≤ z → (p = 3 ∧ z = 2 ∧ m = 6 ∧ D ≤ 6))
    (hc : r = 1 → zOrd = p → p = 3 → c ≤ 1) (hZ0 : z = 0 → mZ = 0 ∧ c = 0)
    (hmZ : zOrd = p → mZ ≤ p ^ r * z) (hcZ : c ≤ mZ)
    (T9n : (p = 3 ∧ m = 2 ∧ w = 0 ∧ zOrd = 1) → D ≤ 2) :
    (r = 1 ∧ z ≤ 1 ∧ (z = 1 → p = 3 ∧ zOrd = 3) ∧ mZ < p ∧ (z = 0 → zOrd = 1) ∧
      (z = 0 → p = 3 ∧ m = 1 ∧ w = 0)) ∨
    (p = 3 ∧ m = 1 ∧ w = 1 ∧ z = 0 ∧ zOrd = 1 ∧ a = 2 ∧ r = 1) ∨
    (p = 3 ∧ m = 2 ∧ w = 1 ∧ z = 1 ∧ zOrd = 3 ∧ mZ = 3 ∧ a = 3 ∧ c = 1 ∧ r = 1) := by
  have hr1 := numerics_r_eq_one hp hr master haD T1a T2 hm hzw hcZ
  subst hr1
  simp only [pow_one] at master hmZ
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
  have hq : q + 3 - 1 = q + 2 := by omega
  have hq' : q + 3 - 2 = q + 1 := by omega
  rw [hq] at master
  rw [hq'] at T3
  rcases Nat.lt_or_ge z 2 with hz2 | hz2
  · rcases Nat.lt_or_ge z 1 with hz1 | hz1
    ·
      have hz : z = 0 := by omega
      obtain ⟨hmZ0, hc0⟩ := hZ0 hz
      have hzO : zOrd = 1 := hz0.1 hz
      subst hmZ0 hc0 hz
      have hnd : ¬ (q + 3) ∣ zOrd := by
        rw [hzO]; intro h; have := Nat.le_of_dvd one_pos h; omega
      by_cases hm7 : m < 7
      · have hD := T1b (Or.inl hm7)
        have hqm : (q + 1) * m ≥ m := Nat.le_mul_of_pos_left m (by omega)
        have hqm2 : (q + 1) * m ≥ 2 * m * 0 + m := by omega
        have h1 : w + (q + 1) * m ≤ 2 := by nlinarith
        have hq0 : q = 0 ∨ q = 1 := by
          rcases Nat.eq_zero_or_pos q with h | h
          · left; exact h
          · right
            by_contra hq1
            have : (q + 1) * m ≥ 3 * 1 := by
              apply Nat.mul_le_mul <;> omega
            omega
        have hm6 : m ≤ 2 := by
          rcases hq0 with h | h <;> subst h <;> omega
        rcases hq0 with h | h
        · subst h
          interval_cases m
          ·
            have hw : w ≤ 1 := by omega
            interval_cases w
            · left; exact ⟨rfl, by omega, by omega, by omega, fun _ => hzO, fun _ => ⟨rfl, rfl, rfl⟩⟩
            · right; left
              refine ⟨rfl, rfl, rfl, rfl, hzO, ?_, rfl⟩
              omega
          ·
            have hw : w = 0 := by omega
            subst hw
            have := T9n ⟨rfl, rfl, rfl, hzO⟩
            omega
        · subst h
          omega
      · have hD : D ≤ m + 2 := T1a
        have hqm : (q + 1) * m ≥ 1 * m := Nat.mul_le_mul (by omega) le_rfl
        have hqm' : (q + 1) * m ≥ 1 * 7 := Nat.mul_le_mul (by omega) (by omega)
        nlinarith
    ·
      have hz : z = 1 := by omega
      subst hz
      have hzO : zOrd ≠ 1 := fun h => by have := hz0.2 h; omega
      have hdvd : q + 3 ∣ zOrd := hzp.resolve_left hzO
      have hD := T1b (Or.inr hdvd)
      have hm2 : 2 ≤ m := T2
      have hw1 : 1 ≤ w := hzw
      rcases T3 rfl with ⟨h3, hz3⟩ | hbig
      · have hq0 : q = 0 := by omega
        subst hq0
        have hc1 := hc rfl (by omega) (by omega)
        have hmZ' := hmZ (by omega)
        norm_num at master hmZ'
        by_cases hmZ3 : mZ < 3
        · left
          exact ⟨rfl, le_rfl, fun _ => ⟨rfl, hz3⟩, by omega, fun h => by omega,
            fun h => by omega⟩
        · have hmZ3' : mZ = 3 := by omega
          subst hmZ3'
          have hm2' : m = 2 := by omega
          have hw1' : w = 1 := by omega
          subst hm2' hw1'
          right; right
          refine ⟨rfl, rfl, rfl, rfl, hz3, rfl, ?_, ?_, rfl⟩ <;> omega
      · exfalso
        simp only [mul_one] at master
        nlinarith
  ·
    exfalso
    obtain ⟨h3, hz, hm6, hD6⟩ := T11 hz2
    subst hz hm6
    have : q = 0 := by omega
    subst this
    omega

theorem numerics_z_cases {p r z zOrd mZ m w : ℕ}
    (hOK : r = 1 ∧ z ≤ 1 ∧ (z = 1 → p = 3 ∧ zOrd = 3) ∧ mZ < p ∧ (z = 0 → zOrd = 1) ∧
      (z = 0 → p = 3 ∧ m = 1 ∧ w = 0)) :
    (z = 0 ∧ zOrd = 1 ∧ p = 3 ∧ m = 1 ∧ w = 0) ∨ (z = 1 ∧ p = 3 ∧ zOrd = 3) := by
  obtain ⟨-, hz, h1, -, h0, h6⟩ := hOK
  rcases Nat.lt_or_ge z 1 with h | h
  · left
    have hz0 : z = 0 := by omega
    exact ⟨hz0, h0 hz0, h6 hz0⟩
  · right; have hz1 : z = 1 := by omega
    exact ⟨hz1, h1 hz1⟩

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
