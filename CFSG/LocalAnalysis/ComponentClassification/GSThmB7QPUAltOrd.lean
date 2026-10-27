module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.ComponentClassification.GSThmB.QPUAlt

theorem pow_le_factorial {p f : ℕ} (hp3 : 3 ≤ p) (hf : 1 ≤ f) :
    (p ^ f) ^ 10 ≤ ((p - 1) * (4 * f) + 1).factorial := by
  rw [← pow_mul]
  rcases Nat.lt_or_ge p 4 with hp4 | hp4
  ·
    obtain rfl : p = 3 := by omega
    have h1 := Nat.factorial_mul_pow_le_factorial (m := 8) (n := 8 * f - 7)
    have h2 : 8 + (8 * f - 7) = (3 - 1) * (4 * f) + 1 := by omega
    rw [h2] at h1
    refine le_trans ?_ h1
    have h3 : (3 : ℕ) ^ 9 ≤ Nat.factorial 8 := by decide
    have h4 : (8 + 1 : ℕ) ^ (8 * f - 7) = 3 ^ (2 * (8 * f - 7)) := by
      rw [pow_mul]
      norm_num
    rw [h4]
    calc (3 : ℕ) ^ (f * 10) ≤ 3 ^ (9 + 2 * (8 * f - 7)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 ^ 9 * 3 ^ (2 * (8 * f - 7)) := pow_add _ _ _
      _ ≤ Nat.factorial 8 * 3 ^ (2 * (8 * f - 7)) := Nat.mul_le_mul_right _ h3
  ·
    set Y := (p - 1) * (4 * f - 1) with hYdef
    set X := (p - 1) * (4 * f) with hXdef
    have hY : X = Y + (p - 1) := by
      rw [hXdef, hYdef, ← Nat.mul_add_one]
      congr 1
      omega
    have h1 := Nat.factorial_mul_pow_le_factorial (m := p - 1) (n := Y + 1)
    have h2 : p - 1 + (Y + 1) = X + 1 := by omega
    rw [h2, show p - 1 + 1 = p by omega] at h1
    refine le_trans ?_ (le_trans (Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)) h1)
    apply Nat.pow_le_pow_right (by omega)
    have h3 : 3 * (4 * f - 1) ≤ Y := Nat.mul_le_mul_right _ (by omega)
    omega

theorem not_dvd_pow_sub_one {p f k : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hk : 1 ≤ k) :
    ¬ p ∣ (p ^ f) ^ k - 1 := by
  intro h
  have h1 : p ∣ (p ^ f) ^ k := dvd_pow (dvd_pow_self p (by omega)) (by omega)
  have h2 : 1 ≤ (p ^ f) ^ k := Nat.one_le_pow _ _ (pow_pos hp.pos _)
  have h3 : p ∣ (p ^ f) ^ k - ((p ^ f) ^ k - 1) := Nat.dvd_sub h1 h
  rw [show (p ^ f) ^ k - ((p ^ f) ^ k - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.mp h3)

theorem factorial_ne_two_mul_card_psp4 {p f m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    m.factorial ≠ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) := by
  intro h
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by omega) p)
  have hA : 1 ≤ (p ^ f) ^ 2 - 1 := by
    have : 9 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  have hB : 1 ≤ (p ^ f) ^ 4 - 1 := by
    have : 81 ≤ (p ^ f) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
    omega
  have hX : ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) ≠ 0 := by positivity
  have hndvd : ¬ p ∣ ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1) := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h1 | h1
    · exact not_dvd_pow_sub_one hp hf (by norm_num) h1
    · exact not_dvd_pow_sub_one hp hf (by norm_num) h1
  have hv : padicValNat p m.factorial = 4 * f := by
    rw [h, padicValNat.mul (by positivity) hX, padicValNat.eq_zero_of_not_dvd hndvd, add_zero,
      ← pow_mul, padicValNat.prime_pow]
    ring
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.factorial_zero] at h
    have h1 : 81 ≤ (p ^ f) ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ (p ^ f) ^ 4 := Nat.pow_le_pow_left hq3 4
    have h2 : 81 ≤ (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) :=
      h1.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hX))
    omega
  have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := p) hm0
  rw [hv] at hlt
  have hlow : (p ^ f) ^ 10 ≤ m.factorial :=
    (pow_le_factorial hp3 hf).trans (Nat.factorial_le (by omega))
  have hup : (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1)) < (p ^ f) ^ 10 := by
    have h1 : (p ^ f) ^ 2 - 1 < (p ^ f) ^ 2 := by omega
    have h2 : (p ^ f) ^ 4 - 1 < (p ^ f) ^ 4 := by omega
    calc (p ^ f) ^ 4 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 4 - 1))
        < (p ^ f) ^ 4 * ((p ^ f) ^ 2 * (p ^ f) ^ 4) := by
          apply Nat.mul_lt_mul_of_pos_left _ (by positivity)
          exact Nat.mul_lt_mul'' h1 h2
      _ = (p ^ f) ^ 10 := by ring
  omega

end CFSG.ComponentClassification.GSThmB.QPUAlt
