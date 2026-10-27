module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

@[expose] def te6Core (q : ℕ) : ℕ := q ^ 4 * (q ^ 2 + 1) * (q * (q - 1) + 1)

@[expose] def o4Val (q : ℕ) : ℕ := ((q ^ 2 - 1) * (q + 1)) * q ^ 2 * ((q - 1) * 2)

section PAdic

variable {p : ℕ}

theorem pow_eq_of_mul_eq (hp : p.Prime) {a b x y : ℕ} (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (h : a * p ^ x = b * p ^ y) : x = y := by
  have := Fact.mk hp
  have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ dvd_zero p)
  have hb0 : b ≠ 0 := fun h0 => hb (h0 ▸ dvd_zero p)
  have := congrArg (padicValNat p) h
  rw [padicValNat.mul ha0 (pow_ne_zero _ hp.ne_zero),
    padicValNat.mul hb0 (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd ha,
    padicValNat.eq_zero_of_not_dvd hb] at this
  simpa using this

theorem not_dvd_add_one (hp : p.Prime) {a : ℕ} (h : p ∣ a) : ¬ p ∣ a + 1 := fun h1 =>
  hp.not_dvd_one ((Nat.dvd_add_right h).mp h1)

theorem not_dvd_sub_one (hp : p.Prime) {a : ℕ} (h : p ∣ a) (ha : 1 ≤ a) : ¬ p ∣ a - 1 :=
  fun h1 => hp.not_dvd_one (by
    have := Nat.dvd_sub h h1
    rwa [Nat.sub_sub_self ha] at this)

theorem not_dvd_two (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ 2 := fun h =>
  hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

end PAdic

section Families

variable {p f q : ℕ}

theorem dvd_of_eq_pow (hf : 1 ≤ f) (hq : q = p ^ f) : p ∣ q := hq ▸ dvd_pow_self p (by omega)

theorem pow_dvd_aux (hpq : p ∣ q) {k : ℕ} (hk : 1 ≤ k) : p ∣ q ^ k := dvd_pow hpq (by omega)

theorem te6Core_mul_o4Val_ne_zero (hq5 : 5 ≤ q) : te6Core q * o4Val q ≠ 0 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 < q ^ 2 := by nlinarith
  unfold te6Core o4Val
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) ?_
    have : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by positivity)) ?_
    omega

theorem not_dvd_mul {a b : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ a * b :=
  fun h => (hp.dvd_mul.mp h).elim ha hb

theorem core_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (hq1 : 1 ≤ q) :
    ¬ p ∣ (q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2)) := by
  have a1 : ¬ p ∣ q ^ 2 + 1 := not_dvd_add_one hp (pow_dvd_aux hpq (by norm_num))
  have a2 : ¬ p ∣ q * (q - 1) + 1 := not_dvd_add_one hp (dvd_mul_of_dvd_left hpq _)
  have a3 : ¬ p ∣ q ^ 2 - 1 :=
    not_dvd_sub_one hp (pow_dvd_aux hpq (by norm_num)) (Nat.one_le_pow _ _ hq1)
  have a4 : ¬ p ∣ q + 1 := not_dvd_add_one hp hpq
  have a5 : ¬ p ∣ q - 1 := not_dvd_sub_one hp hpq hq1
  have a6 : ¬ p ∣ 2 := not_dvd_two hp hp2
  exact not_dvd_mul hp (not_dvd_mul hp a1 a2)
    (not_dvd_mul hp (not_dvd_mul hp a3 a4) (not_dvd_mul hp a5 a6))

theorem pow_add_one_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (k : ℕ) :
    ¬ p ∣ q ^ k + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using not_dvd_two hp hp2
  · exact not_dvd_add_one hp (pow_dvd_aux hpq hk)

theorem pow_sub_one_coprime (hp : p.Prime) (hpq : p ∣ q) (hq1 : 1 ≤ q) {k : ℕ} (hk : 1 ≤ k) :
    ¬ p ∣ q ^ k - 1 :=
  not_dvd_sub_one hp (pow_dvd_aux hpq hk) (Nat.one_le_pow _ _ hq1)

theorem plus_impossible (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
        (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j)))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
  have hR : 2 * (((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
        (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j))) =
      (2 * ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) * ((q ^ (j + 1) - 1) * (q ^ j + 1)))) *
        p ^ (f * (4 * j + 2)) := by
    have e : p ^ (f * (4 * j + 2)) = q ^ (4 * j + 2) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) *
      ((q ^ (j + 1) - 1) * (q ^ j + 1))) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
        (pow_add_one_coprime hp hp2 hpq _))
      (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
        (pow_add_one_coprime hp hp2 hpq _)))
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have hj : j = 1 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
    omega
  subst hj
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq3 : 1 ≤ q ^ (1 + 1 + 1) := Nat.one_le_pow _ _ hq1
  have hq4 : 1 ≤ q ^ (1 + 1) := Nat.one_le_pow _ _ hq1
  have hq5' : 1 ≤ q ^ 1 := Nat.one_le_pow _ _ hq1
  unfold te6Core o4Val at h
  zify [hq1, hq2, hq3, hq4, hq5', Nat.one_le_pow 1 q hq1] at h
  have hqz : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2z : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by
    have : (25 : ℤ) ≤ (q : ℤ) ^ 2 := by
      have : (5 : ℤ) ≤ q := by exact_mod_cast hq5
      nlinarith
    linarith
  have hpos : (0 : ℤ) < (q : ℤ) ^ 7 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) ^ 2 := by positivity
  have h0 : -4 * (q : ℤ) ^ 7 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) ^ 2 = 0 := by
    linear_combination h
  linarith

theorem minus_eq (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f) (hq5 : 5 ≤ q)
    {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
        (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1))))) : j = 0 := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
  have hR : 2 * (((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
        (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1)))) =
      (2 * ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
        ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)))) * p ^ (f * (4 * j + 6)) := by
    have e : p ^ (f * (4 * j + 6)) = q ^ (4 * j + 6) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1))) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
        (pow_sub_one_coprime hp hpq hq1 (by omega)))
      (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
        (pow_sub_one_coprime hp hpq hq1 (by omega))))
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem odd_impossible (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq5 : 5 ≤ q) {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1)))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
  have hR : 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1))) =
      (2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1))) * p ^ (f * (4 * j + 4)) := by
    have e : p ^ (f * (4 * j + 4)) = q ^ (4 * j + 4) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1)) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (pow_sub_one_coprime hp hpq hq1 (by omega)) (pow_sub_one_coprime hp hpq hq1 (by omega)))
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end Families

end CFSG.ClassicalInvolution.RouteD.NonClassical
