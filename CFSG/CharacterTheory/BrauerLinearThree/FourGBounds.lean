module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.BrauerLinearThree

theorem bounds_plus_one {q x : ℚ} (hq : 7 ≤ q) (hx : 5 * q < x) :
    5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2) < (q - 1) / q * (x * (x + 1) / (x + q) ^ 2) ∧
      (q - 1) / q * (x * (x + 1) / (x + q) ^ 2) < 5 * (5 * q + 1) * (q + 1) / (16 * q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have hxq : 0 < x + q := by linarith
  have e : (q - 1) / q * (x * (x + 1) / (x + q) ^ 2) = (q - 1) * (x * (x + 1)) /
      (q * (x + q) ^ 2) := by
    field_simp
  rw [e]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : 36 * q * (x * (x + 1)) - 5 * (5 * q + 1) * (x + q) ^ 2 =
        (x - 5 * q) * ((11 * q - 5) * x + 5 * q ^ 2 + q) := by ring
    have hpos : 0 < (x - 5 * q) * ((11 * q - 5) * x + 5 * q ^ 2 + q) := by
      apply mul_pos (by linarith)
      nlinarith
    have hq1 : 0 < q - 1 := by linarith
    nlinarith [mul_pos (mul_pos hq1 hq0) hpos]
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : x * (x + 1) < (x + q) ^ 2 := by nlinarith
    have h2 : 16 * q ^ 2 * (q - 1) < 5 * (5 * q + 1) * (q + 1) * q := by nlinarith
    have hq1 : 0 < q - 1 := by linarith
    have hxq2 : 0 < (x + q) ^ 2 := by positivity
    calc (q - 1) * (x * (x + 1)) * (16 * q ^ 2) = ((q - 1) * (16 * q ^ 2)) * (x * (x + 1)) := by
          ring
      _ < ((q - 1) * (16 * q ^ 2)) * (x + q) ^ 2 :=
          mul_lt_mul_of_pos_left h1 (by positivity)
      _ = (16 * q ^ 2 * (q - 1)) * (x + q) ^ 2 := by ring
      _ < (5 * (5 * q + 1) * (q + 1) * q) * (x + q) ^ 2 := mul_lt_mul_of_pos_right h2 hxq2
      _ = 5 * (5 * q + 1) * (q + 1) * (q * (x + q) ^ 2) := by ring

theorem bounds_minus_one {q x : ℚ} (hq : 7 ≤ q) (hx : 5 * q < x) :
    5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2) < (q - 1) / q * (x * (x - 1) / (x - q) ^ 2) ∧
      (q - 1) / q * (x * (x - 1) / (x - q) ^ 2) < 5 * (5 * q + 1) * (q + 1) / (16 * q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have hxq : 0 < x - q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have e : (q - 1) / q * (x * (x - 1) / (x - q) ^ 2) = (q - 1) * (x * (x - 1)) /
      (q * (x - q) ^ 2) := by
    field_simp
  rw [e]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (x - q) ^ 2 < x * (x - 1) := by nlinarith
    have h2 : 5 * (5 * q + 1) * q < 36 * q ^ 2 := by nlinarith
    have h3 : 5 * (5 * q + 1) * (q - 1) * (q * (x - q) ^ 2) <
        36 * q ^ 2 * ((q - 1) * (x - q) ^ 2) := by
      have hpos : 0 < (q - 1) * (x - q) ^ 2 := by positivity
      nlinarith
    have h4 : 36 * q ^ 2 * ((q - 1) * (x - q) ^ 2) < 36 * q ^ 2 * ((q - 1) * (x * (x - 1))) := by
      have := mul_lt_mul_of_pos_left h1 hq1
      nlinarith
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : 5 * (5 * q - 1) * (x - q) ^ 2 - 16 * q * (x * (x - 1)) =
        (x - 5 * q) * ((9 * q - 5) * x - 5 * q ^ 2 + q) := by ring
    have hpos : 0 < (x - 5 * q) * ((9 * q - 5) * x - 5 * q ^ 2 + q) := by
      apply mul_pos (by linarith)
      nlinarith
    have h1 : 16 * q * (x * (x - 1)) < 5 * (5 * q - 1) * (x - q) ^ 2 := by linarith
    have h2 : (q - 1) * (5 * q - 1) < (5 * q + 1) * (q + 1) := by nlinarith
    have h3 : (q - 1) * (x * (x - 1)) * (16 * q ^ 2) <
        (q - 1) * (5 * (5 * q - 1) * (x - q) ^ 2) * q := by
      calc (q - 1) * (x * (x - 1)) * (16 * q ^ 2) = ((q - 1) * q) * (16 * q * (x * (x - 1))) := by
            ring
        _ < ((q - 1) * q) * (5 * (5 * q - 1) * (x - q) ^ 2) :=
            mul_lt_mul_of_pos_left h1 (mul_pos hq1 hq0)
        _ = (q - 1) * (5 * (5 * q - 1) * (x - q) ^ 2) * q := by ring
    have hpos' : 0 < q * (x - q) ^ 2 := by positivity
    have h4 : (q - 1) * (5 * (5 * q - 1) * (x - q) ^ 2) * q <
        5 * (5 * q + 1) * (q + 1) * (q * (x - q) ^ 2) := by
      calc (q - 1) * (5 * (5 * q - 1) * (x - q) ^ 2) * q =
          ((q - 1) * (5 * q - 1)) * (5 * (q * (x - q) ^ 2)) := by ring
        _ < ((5 * q + 1) * (q + 1)) * (5 * (q * (x - q) ^ 2)) :=
            mul_lt_mul_of_pos_right h2 (by positivity)
        _ = 5 * (5 * q + 1) * (q + 1) * (q * (x - q) ^ 2) := by ring
    linarith

theorem bounds_plus_two {q x : ℚ} (hq : 7 ≤ q) (hx : 5 * q < x) :
    5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2) < (q + 1) / q * (x * (x + 1) / (x - q) ^ 2) ∧
      (q + 1) / q * (x * (x + 1) / (x - q) ^ 2) < 5 * (5 * q + 1) * (q + 1) / (16 * q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have hxq : 0 < x - q := by linarith
  have e : (q + 1) / q * (x * (x + 1) / (x - q) ^ 2) = (q + 1) * (x * (x + 1)) /
      (q * (x - q) ^ 2) := by
    field_simp
  rw [e]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : (x - q) ^ 2 < x * (x + 1) := by nlinarith
    have h2 : 5 * (5 * q + 1) * (q - 1) * q < 36 * q ^ 2 * (q + 1) := by nlinarith
    have hpos : 0 < (x - q) ^ 2 := by positivity
    nlinarith [mul_lt_mul_of_pos_left h1 (show (0 : ℚ) < 36 * q ^ 2 * (q + 1) by positivity)]
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : 5 * (5 * q + 1) * (x - q) ^ 2 - 16 * q * (x * (x + 1)) =
        (x - 5 * q) * ((9 * q + 5) * x - 5 * q ^ 2 - q) := by ring
    have hpos : 0 < (x - 5 * q) * ((9 * q + 5) * x - 5 * q ^ 2 - q) := by
      apply mul_pos (by linarith)
      nlinarith
    have hq1 : 0 < q + 1 := by linarith
    nlinarith [mul_pos (mul_pos hq1 hq0) hpos]

theorem bounds_minus_two {q x : ℚ} (hq : 7 ≤ q) (hx : 5 * q < x) :
    5 * (5 * q + 1) * (q - 1) / (36 * q ^ 2) < (q + 1) / q * (x * (x - 1) / (x + q) ^ 2) ∧
      (q + 1) / q * (x * (x - 1) / (x + q) ^ 2) < 5 * (5 * q + 1) * (q + 1) / (16 * q ^ 2) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 < x := by linarith
  have hxq : 0 < x + q := by linarith
  have hq1 : 0 < q + 1 := by linarith
  have e : (q + 1) / q * (x * (x - 1) / (x + q) ^ 2) = (q + 1) * (x * (x - 1)) /
      (q * (x + q) ^ 2) := by
    field_simp
  rw [e]
  constructor
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have key : 36 * q * (x * (x - 1)) - 5 * (5 * q - 1) * (x + q) ^ 2 =
        (x - 5 * q) * ((11 * q + 5) * x + 5 * q ^ 2 - q) := by ring
    have hpos : 0 < (x - 5 * q) * ((11 * q + 5) * x + 5 * q ^ 2 - q) := by
      apply mul_pos (by linarith)
      nlinarith
    have h1 : 5 * (5 * q - 1) * (x + q) ^ 2 < 36 * q * (x * (x - 1)) := by linarith
    have h2 : (5 * q + 1) * (q - 1) < (5 * q - 1) * (q + 1) := by nlinarith
    have hpos' : 0 < (x + q) ^ 2 := by positivity
    have h3 : 5 * (5 * q + 1) * (q - 1) * (q * (x + q) ^ 2) <
        5 * (5 * q - 1) * (q + 1) * (q * (x + q) ^ 2) := by
      calc 5 * (5 * q + 1) * (q - 1) * (q * (x + q) ^ 2) =
          ((5 * q + 1) * (q - 1)) * (5 * (q * (x + q) ^ 2)) := by ring
        _ < ((5 * q - 1) * (q + 1)) * (5 * (q * (x + q) ^ 2)) :=
            mul_lt_mul_of_pos_right h2 (by positivity)
        _ = 5 * (5 * q - 1) * (q + 1) * (q * (x + q) ^ 2) := by ring
    have h4 : 5 * (5 * q - 1) * (q + 1) * (q * (x + q) ^ 2) <
        36 * q ^ 2 * ((q + 1) * (x * (x - 1))) := by
      calc 5 * (5 * q - 1) * (q + 1) * (q * (x + q) ^ 2) =
          ((q + 1) * q) * (5 * (5 * q - 1) * (x + q) ^ 2) := by ring
        _ < ((q + 1) * q) * (36 * q * (x * (x - 1))) :=
            mul_lt_mul_of_pos_left h1 (mul_pos hq1 hq0)
        _ = 36 * q ^ 2 * ((q + 1) * (x * (x - 1))) := by ring
    linarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h1 : x * (x - 1) < (x + q) ^ 2 := by nlinarith
    have h2 : 16 * q ^ 2 * (q + 1) < 5 * (5 * q + 1) * (q + 1) * q := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left h1 (show (0 : ℚ) < (q + 1) * (16 * q ^ 2) by positivity)]

theorem sq_le_of_mul_eq {p f x k m : ℕ} (hp : p.Prime) (hk : ¬ p ∣ k) (hx : 0 < x)
    (hmul : x * (x + k) = (p ^ f) ^ 2 * m) :
    (p ^ f) ^ 2 ≤ x ∨ (p ^ f) ^ 2 ≤ x + k := by
  have hdvd : (p ^ f) ^ 2 ∣ x * (x + k) := ⟨m, hmul⟩
  rw [← pow_mul] at hdvd
  by_cases hpx : p ∣ x
  · left
    have hpy : ¬ p ∣ x + k := fun h => hk ((Nat.dvd_add_right hpx).mp h)
    have hcop : Nat.Coprime (p ^ (f * 2)) (x + k) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpy)
    have := Nat.le_of_dvd hx ((hcop.dvd_mul_right).mp hdvd)
    rwa [← pow_mul]
  · right
    have hcop : Nat.Coprime (p ^ (f * 2)) x :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx)
    have := Nat.le_of_dvd (by omega) ((hcop.dvd_mul_left).mp hdvd)
    rwa [← pow_mul]

theorem three_pow_le_of_mul_eq {f x : ℕ} (hx : 0 < x)
    (hmul : x * (x + 24) = (3 ^ f) ^ 2 * 25) (hf : 1 ≤ f) :
    3 ^ (2 * f - 1) ≤ x ∨ 3 ^ (2 * f - 1) ≤ x + 24 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hv : padicValNat 3 x + padicValNat 3 (x + 24) = 2 * f := by
    have h := congrArg (padicValNat 3) hmul
    rw [padicValNat.mul (by omega) (by omega), padicValNat.mul (by positivity) (by norm_num),
      ← pow_mul, padicValNat.prime_pow, show padicValNat 3 25 = 0 from
        padicValNat.eq_zero_of_not_dvd (by norm_num)] at h
    omega
  have hnot : padicValNat 3 x ≤ 1 ∨ padicValNat 3 (x + 24) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have d1 : 3 ^ 2 ∣ x := (padicValNat_dvd_iff_le (by omega)).mpr h1
    have d2 : 3 ^ 2 ∣ x + 24 := (padicValNat_dvd_iff_le (by omega)).mpr h2
    have := (Nat.dvd_add_right d1).mp d2
    norm_num at this
  rcases hnot with h | h
  · right
    have hd : 3 ^ (2 * f - 1) ∣ x + 24 :=
      (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    exact Nat.le_of_dvd (by omega) hd
  · left
    have hd : 3 ^ (2 * f - 1) ∣ x :=
      (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    exact Nat.le_of_dvd hx hd

theorem false_of_mul_eq_of_le {p f x m : ℕ} (hp : p.Prime) (hq7 : 7 ≤ p ^ f)
    (hq4 : p ^ f % 4 = 3) (hx : 0 < x) (hm : m = 9 ∨ m = 17 ∨ m = 25)
    (hmul : x * (x + (m - 1)) = (p ^ f) ^ 2 * m) (hx5 : x + (m - 1) ≤ 5 * p ^ f) : False := by
  have hq0 : 0 < p ^ f := by positivity
  have hsq : 5 * p ^ f < (p ^ f) ^ 2 := by nlinarith
  by_cases hpk : p ∣ m - 1
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2 : ℕ) ∣ 2 ^ f := dvd_pow_self 2 (by rintro rfl; norm_num at hq7)
      omega
    have hp3 : p = 3 ∧ m = 25 := by
      rcases hm with rfl | rfl | rfl
      · exfalso
        have h8 : p ∣ 2 ^ 3 := by simpa using hpk
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8))
      · exfalso
        have h16 : p ∣ 2 ^ 4 := by simpa using hpk
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h16))
      · refine ⟨?_, rfl⟩
        have h24 : p ∣ 2 ^ 3 * 3 := by simpa using hpk
        rcases (Nat.Prime.dvd_mul hp).mp h24 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
            (hp.dvd_of_dvd_pow h)) hp2
        · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    obtain ⟨rfl, rfl⟩ := hp3
    have hf3 : 3 ≤ f := by
      by_contra hcon
      push Not at hcon
      interval_cases f <;> (revert hq7 hq4; norm_num)
    have hle := three_pow_le_of_mul_eq hx (by simpa using hmul) (by omega)
    have hbig : 5 * 3 ^ f < 3 ^ (2 * f - 1) := by
      have e : 3 ^ (2 * f - 1) = 3 ^ (f - 1) * 3 ^ f := by
        rw [← pow_add]; congr 1; omega
      have h9 : 9 ≤ 3 ^ (f - 1) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [e]
      have : 0 < 3 ^ f := by positivity
      nlinarith
    rcases hle with h | h <;> omega
  · rcases sq_le_of_mul_eq hp hpk hx hmul with h | h <;> omega

theorem false_of_small_degrees {p f q f₁ f₂ f₃ : ℕ} {δ₁ δ₂ δ₃ : ℤ} (hp : p.Prime)
    (hq : q = p ^ f) (hq7 : 7 ≤ q) (hq4 : q % 4 = 3) (h1 : 1 < f₁) (h2 : 1 < f₂) (h3 : 1 < f₃)
    (hδ : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hprod : f₁ * f₂ = q ^ 2 * f₃) (hlin : (f₃ : ℤ) + δ₁ * f₂ + δ₂ * f₁ + δ₃ = 0)
    (hcong : (f₃ : ℤ) ≡ -δ₃ [ZMOD 8]) (hf₁ : f₁ ≤ 5 * q) (hf₂ : f₂ ≤ 5 * q) : False := by
  have hq0 : 0 < q := by omega
  have h25 : f₃ ≤ 25 := by
    have : q ^ 2 * f₃ ≤ q ^ 2 * 25 := by
      rw [← hprod]
      calc f₁ * f₂ ≤ (5 * q) * (5 * q) := Nat.mul_le_mul hf₁ hf₂
        _ = q ^ 2 * 25 := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  subst hq
  rcases hδ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    have hsum : (f₁ : ℤ) + f₂ = f₃ + 1 := by linarith
    have hprodZ : (f₁ : ℤ) * f₂ = (p ^ f : ℕ) ^ 2 * f₃ := by exact_mod_cast hprod
    have hq7' : (7 : ℤ) ≤ (p ^ f : ℕ) := by exact_mod_cast hq7
    have h3' : (1 : ℤ) < f₃ := by exact_mod_cast h3
    have h25' : (f₃ : ℤ) ≤ 25 := by exact_mod_cast h25
    have hsq : (0 : ℤ) ≤ ((f₁ : ℤ) - f₂) ^ 2 := sq_nonneg _
    have hq2 : (49 : ℤ) ≤ ((p ^ f : ℕ) : ℤ) ^ 2 := by nlinarith
    nlinarith
  ·
    have hm : f₃ = 9 ∨ f₃ = 17 ∨ f₃ = 25 := by
      have : (f₃ : ℤ) % 8 = 1 := by
        have := Int.emod_emod_of_dvd (f₃ : ℤ) (show (8 : ℤ) ∣ 8 from dvd_refl _)
        rw [Int.ModEq] at hcong
        omega
      omega
    have hy : f₂ = f₁ + (f₃ - 1) := by omega
    rw [hy] at hprod hf₂
    exact false_of_mul_eq_of_le hp hq7 hq4 (by omega) hm hprod hf₂
  ·
    have hm : f₃ = 9 ∨ f₃ = 17 ∨ f₃ = 25 := by
      have : (f₃ : ℤ) % 8 = 1 := by
        rw [Int.ModEq] at hcong
        omega
      omega
    have hy : f₁ = f₂ + (f₃ - 1) := by omega
    rw [hy, mul_comm] at hprod
    rw [hy] at hf₁
    exact false_of_mul_eq_of_le hp hq7 hq4 (by omega) hm hprod hf₁

theorem order_parameter_bounds {p f q f₁ f₂ f₃ : ℕ} {δ₁ δ₂ δ₃ : ℤ} {μ : ℚ} (hp : p.Prime)
    (hq : q = p ^ f) (hq7 : 7 ≤ q) (hq4 : q % 4 = 3) (h1 : 1 < f₁) (h2 : 1 < f₂) (h3 : 1 < f₃)
    (hδ : (δ₁ = -1 ∧ δ₂ = -1 ∧ δ₃ = 1) ∨ (δ₁ = -1 ∧ δ₂ = 1 ∧ δ₃ = -1) ∨
      (δ₁ = 1 ∧ δ₂ = -1 ∧ δ₃ = -1))
    (hprod : f₁ * f₂ = q ^ 2 * f₃)
    (hrel : (1 : ℚ) + δ₁ * q ^ 2 / f₁ + δ₂ * q ^ 2 / f₂ + δ₃ / f₃ = 0)
    (hcong : (f₃ : ℤ) ≡ -δ₃ [ZMOD 8])
    (hμ₁ : μ = (q - 1) / q * (f₁ * (f₁ + δ₁) / (f₁ + δ₁ * q) ^ 2))
    (hμ₂ : μ = (q + 1) / q * (f₂ * (f₂ + δ₂) / (f₂ - δ₂ * q) ^ 2)) :
    5 * (5 * (q : ℚ) + 1) * (q - 1) / (36 * q ^ 2) < μ ∧
      μ < 5 * (5 * (q : ℚ) + 1) * (q + 1) / (16 * q ^ 2) := by
  have hq7' : (7 : ℚ) ≤ q := by exact_mod_cast hq7
  have hlin : (f₃ : ℤ) + δ₁ * f₂ + δ₂ * f₁ + δ₃ = 0 := by
    have hf1 : (f₁ : ℚ) ≠ 0 := by positivity
    have hf2 : (f₂ : ℚ) ≠ 0 := by positivity
    have hf3 : (f₃ : ℚ) ≠ 0 := by positivity
    have hprodQ : (f₁ : ℚ) * f₂ = q ^ 2 * f₃ := by exact_mod_cast hprod
    have e1 : (q : ℚ) ^ 2 / f₁ = f₂ / f₃ := by
      rw [div_eq_div_iff hf1 hf3]; linarith
    have e2 : (q : ℚ) ^ 2 / f₂ = f₁ / f₃ := by
      rw [div_eq_div_iff hf2 hf3]; linarith
    have h : (f₃ : ℚ) + δ₁ * f₂ + δ₂ * f₁ + δ₃ = 0 := by
      rw [mul_div_assoc, mul_div_assoc, e1, e2] at hrel
      field_simp at hrel
      linarith
    exact_mod_cast h
  have hδ₁ : δ₁ = 1 ∨ δ₁ = -1 := by rcases hδ with h | h | h <;> simp [h.1]
  have hδ₂ : δ₂ = 1 ∨ δ₂ = -1 := by rcases hδ with h | h | h <;> simp [h.2.1]
  by_cases hA : 5 * q < f₁
  · have hA' : 5 * (q : ℚ) < f₁ := by exact_mod_cast hA
    rw [hμ₁]
    rcases hδ₁ with rfl | rfl
    · have := bounds_plus_one hq7' hA'
      simpa using this
    · have := bounds_minus_one hq7' hA'
      simpa [sub_eq_add_neg] using this
  by_cases hB : 5 * q < f₂
  · have hB' : 5 * (q : ℚ) < f₂ := by exact_mod_cast hB
    rw [hμ₂]
    rcases hδ₂ with rfl | rfl
    · have := bounds_plus_two hq7' hB'
      simpa [sub_eq_add_neg] using this
    · have := bounds_minus_two hq7' hB'
      simpa [sub_eq_add_neg] using this
  exact (false_of_small_degrees hp hq hq7 hq4 h1 h2 h3 hδ hprod hlin hcong (by omega)
    (by omega)).elim

end CFSG.BrauerLinearThree
