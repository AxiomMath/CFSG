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
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.RowLie

variable {q s : ℕ}

theorem ordProj_eq_one_of_not_dvd {n : ℕ} (h : ¬ s ∣ n) : ordProj[s] n = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

theorem two_mul_ordProj_le (hs : s.Prime) (hs2 : s ≠ 2) {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) :
    2 * ordProj[s] n ≤ n := by
  have hd : ordProj[s] n ∣ n := Nat.ordProj_dvd n s
  have hcop : Nat.Coprime 2 (ordProj[s] n) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hs).mpr (Ne.symm hs2))
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (hcop.mul_dvd_of_dvd_of_dvd h2 hd)

theorem not_dvd_two (hs : s.Prime) (hs2 : s ≠ 2) : ¬ s ∣ 2 := fun h =>
  hs2 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h)

theorem sq_add_one_eq (hq : 1 ≤ q) : q ^ 2 + 1 = (q - 1) * (q + 1) + 2 := by
  have h : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    zify [hq, Nat.one_le_pow 2 q hq]
    ring
  rw [h]
  have : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq
  omega

theorem sq_sub_add_one_eq : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
  have h : q * (q - 1) = q ^ 2 - q := by
    rw [Nat.mul_sub, mul_one, sq]
  rw [h]

section Exclusions

theorem false_of_dvd_sub_of_dvd_add (hs : s.Prime) (hs2 : s ≠ 2) (hq : 1 ≤ q)
    (h1 : s ∣ q - 1) (h2 : s ∣ q + 1) : False := by
  have : q + 1 = (q - 1) + 2 := by omega
  rw [this] at h2
  exact not_dvd_two hs hs2 ((Nat.dvd_add_right h1).mp h2)

theorem false_of_dvd_sub_of_dvd_sq (hs : s.Prime) (hs2 : s ≠ 2) (hq : 1 ≤ q)
    (h1 : s ∣ q - 1) (h2 : s ∣ q ^ 2 + 1) : False := by
  rw [sq_add_one_eq hq] at h2
  exact not_dvd_two hs hs2 ((Nat.dvd_add_right (dvd_mul_of_dvd_left h1 _)).mp h2)

theorem false_of_dvd_add_of_dvd_sq (hs : s.Prime) (hs2 : s ≠ 2) (hq : 1 ≤ q)
    (h1 : s ∣ q + 1) (h2 : s ∣ q ^ 2 + 1) : False := by
  rw [sq_add_one_eq hq] at h2
  exact not_dvd_two hs hs2 ((Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp h2)

theorem false_of_dvd_add_of_dvd_d (hs : s.Prime) (h1 : s ∣ q + 1) (h2 : s ∣ q ^ 2 + q + 1) :
    False := by
  have : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
  rw [this] at h2
  exact hs.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp h2))

theorem false_of_dvd_sub_of_dvd_e (hs : s.Prime) (h1 : s ∣ q - 1) (h2 : s ∣ q ^ 2 - q + 1) :
    False := by
  rw [sq_sub_add_one_eq] at h2
  exact hs.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_of_dvd_right h1 _)).mp h2))

theorem false_of_dvd_sq_of_dvd_d (hsq : ¬ s ∣ q) (h1 : s ∣ q ^ 2 + 1)
    (h2 : s ∣ q ^ 2 + q + 1) : False := by
  have : q ^ 2 + q + 1 = (q ^ 2 + 1) + q := by ring
  rw [this] at h2
  exact hsq ((Nat.dvd_add_right h1).mp h2)

theorem false_of_dvd_sq_of_dvd_e (hsq : ¬ s ∣ q) (hq : 1 ≤ q) (h1 : s ∣ q ^ 2 + 1)
    (h2 : s ∣ q ^ 2 - q + 1) : False := by
  have hle : q ≤ q ^ 2 := by nlinarith [hq]
  have : q ^ 2 + 1 = (q ^ 2 - q + 1) + q := by omega
  rw [this] at h1
  exact hsq ((Nat.dvd_add_right h2).mp h1)

theorem false_of_dvd_d_of_dvd_e (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q) (hq : 1 ≤ q)
    (h1 : s ∣ q ^ 2 + q + 1) (h2 : s ∣ q ^ 2 - q + 1) : False := by
  have hle : q ≤ q ^ 2 := by nlinarith [hq]
  have : q ^ 2 + q + 1 = (q ^ 2 - q + 1) + 2 * q := by omega
  rw [this] at h1
  have h3 := (Nat.dvd_add_right h2).mp h1
  rcases (Nat.Prime.dvd_mul hs).mp h3 with h | h
  · exact not_dvd_two hs hs2 h
  · exact hsq h

theorem ordProj_d_le_three (hs : s.Prime) (hsq : ¬ s ∣ q) (hq : 1 ≤ q) (h1 : s ∣ q - 1) :
    ordProj[s] (q ^ 2 + q + 1) ≤ 3 := by
  by_cases h2 : s ∣ q ^ 2 + q + 1
  · have he : q ^ 2 + q + 1 = (q - 1) ^ 2 + 3 * q := by
      zify [hq]
      ring
    have h3 : s ∣ 3 * q := by
      rw [he] at h2
      exact (Nat.dvd_add_right (dvd_pow h1 two_ne_zero)).mp h2
    have hs3 : s = 3 := by
      rcases (Nat.Prime.dvd_mul hs).mp h3 with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h
      · exact absurd h hsq
    subst hs3
    have hn9 : ¬ 3 ^ 2 ∣ q ^ 2 + q + 1 := by
      intro h9
      obtain ⟨k, hk⟩ := h1
      have hq9 : q ^ 2 + q + 1 = 9 * k ^ 2 + 3 * q := by rw [he, hk]; ring
      rw [hq9, show (3 : ℕ) ^ 2 = 9 by norm_num] at h9
      have h10 : 9 ∣ 3 * q := (Nat.dvd_add_right (dvd_mul_right 9 _)).mp h9
      exact hsq (by omega)
    have hv : (q ^ 2 + q + 1).factorization 3 ≤ 1 := by
      by_contra hv
      push Not at hv
      exact hn9 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by positivity)).mpr hv)
    calc ordProj[3] (q ^ 2 + q + 1) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hv
      _ = 3 := by norm_num
  · rw [ordProj_eq_one_of_not_dvd h2]
    norm_num

theorem ordProj_e_le_three (hs : s.Prime) (hsq : ¬ s ∣ q) (hq : 1 ≤ q) (h1 : s ∣ q + 1) :
    ordProj[s] (q ^ 2 - q + 1) ≤ 3 := by
  have hle : q ≤ q ^ 2 := by nlinarith [hq]
  by_cases h2 : s ∣ q ^ 2 - q + 1
  · have he : (q ^ 2 - q + 1) + 3 * q = (q + 1) ^ 2 := by
      zify [hle]
      ring
    have h3 : s ∣ 3 * q := by
      have h4 : s ∣ (q + 1) ^ 2 := dvd_pow h1 two_ne_zero
      rw [← he] at h4
      exact (Nat.dvd_add_right h2).mp h4
    have hs3 : s = 3 := by
      rcases (Nat.Prime.dvd_mul hs).mp h3 with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h
      · exact absurd h hsq
    subst hs3
    have hn9 : ¬ 3 ^ 2 ∣ q ^ 2 - q + 1 := by
      intro h9
      obtain ⟨k, hk⟩ := h1
      have h9' : 9 ∣ (q ^ 2 - q + 1) + 3 * q := by
        rw [he, hk]
        exact ⟨k ^ 2, by ring⟩
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at h9
      have h10 : 9 ∣ 3 * q := (Nat.dvd_add_right h9).mp h9'
      exact hsq (by omega)
    have hv : (q ^ 2 - q + 1).factorization 3 ≤ 1 := by
      by_contra hv
      push Not at hv
      exact hn9 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by omega)).mpr hv)
    calc ordProj[3] (q ^ 2 - q + 1) ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hv
      _ = 3 := by norm_num
  · rw [ordProj_eq_one_of_not_dvd h2]
    norm_num

end Exclusions

theorem cyc_ne_zero (hq : 2 ≤ q) (a b c d e : ℕ) :
    (q - 1) ^ a * (q + 1) ^ b * (q ^ 2 + 1) ^ c * (q ^ 2 + q + 1) ^ d *
      (q ^ 2 - q + 1) ^ e ≠ 0 := by
  have hle : q ≤ q ^ 2 := by nlinarith
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_ <;>
    apply pow_ne_zero <;> omega

theorem ordProj_pow (n k : ℕ) : ordProj[s] (n ^ k) = (ordProj[s] n) ^ k := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, pow_mul']

theorem ordProj_cyc_le (hq : 3 ≤ q) (hqo : Odd q) (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q)
    {a b c d e : ℕ} (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 1) (hd : d ≤ 1) (he : e ≤ 1) :
    ordProj[s] ((q - 1) ^ a * (q + 1) ^ b * (q ^ 2 + 1) ^ c * (q ^ 2 + q + 1) ^ d *
      (q ^ 2 - q + 1) ^ e) ≤ (q + 1) ^ 3 := by
  have hq1 : 1 ≤ q := by omega
  have hle : q ≤ q ^ 2 := by nlinarith
  have hA0 : q - 1 ≠ 0 := by omega
  have hB0 : q + 1 ≠ 0 := by omega
  have hC0 : q ^ 2 + 1 ≠ 0 := by positivity
  have hD0 : q ^ 2 + q + 1 ≠ 0 := by positivity
  have hE0 : q ^ 2 - q + 1 ≠ 0 := by omega
  have hP1 : (q - 1) ^ a ≠ 0 := pow_ne_zero _ hA0
  have hP2 : (q + 1) ^ b ≠ 0 := pow_ne_zero _ hB0
  have hP3 : (q ^ 2 + 1) ^ c ≠ 0 := pow_ne_zero _ hC0
  have hP4 : (q ^ 2 + q + 1) ^ d ≠ 0 := pow_ne_zero _ hD0
  have hP5 : (q ^ 2 - q + 1) ^ e ≠ 0 := pow_ne_zero _ hE0
  rw [Nat.ordProj_mul s (mul_ne_zero (mul_ne_zero (mul_ne_zero hP1 hP2) hP3) hP4) hP5,
    Nat.ordProj_mul s (mul_ne_zero (mul_ne_zero hP1 hP2) hP3) hP4,
    Nat.ordProj_mul s (mul_ne_zero hP1 hP2) hP3, Nat.ordProj_mul s hP1 hP2,
    ordProj_pow, ordProj_pow, ordProj_pow, ordProj_pow, ordProj_pow]
  have hpos : ∀ n : ℕ, 0 < ordProj[s] n := fun n => pow_pos hs.pos _
  have hA2 : 2 * ordProj[s] (q - 1) ≤ q - 1 :=
    two_mul_ordProj_le hs hs2 hA0 (Nat.Odd.sub_odd hqo odd_one).two_dvd
  have hB2 : 2 * ordProj[s] (q + 1) ≤ q + 1 :=
    two_mul_ordProj_le hs hs2 hB0 (hqo.add_odd odd_one).two_dvd
  have hC : ordProj[s] (q ^ 2 + 1) ≤ q ^ 2 + 1 := Nat.ordProj_le s hC0
  have hD : ordProj[s] (q ^ 2 + q + 1) ≤ q ^ 2 + q + 1 := Nat.ordProj_le s hD0
  have hE : ordProj[s] (q ^ 2 - q + 1) ≤ q ^ 2 - q + 1 := Nat.ordProj_le s hE0
  set A := ordProj[s] (q - 1) with hAdef
  set B := ordProj[s] (q + 1) with hBdef
  set C := ordProj[s] (q ^ 2 + 1) with hCdef
  set D := ordProj[s] (q ^ 2 + q + 1) with hDdef
  set E := ordProj[s] (q ^ 2 - q + 1) with hEdef
  have hle3 : ∀ {x k : ℕ}, 0 < x → k ≤ 3 → x ^ k ≤ x ^ 3 := fun hx hk =>
    Nat.pow_le_pow_right hx hk
  have hle1 : ∀ {x k : ℕ}, 0 < x → k ≤ 1 → x ^ k ≤ x := fun hx hk =>
    (Nat.pow_le_pow_right hx hk).trans_eq (pow_one _)
  have hq3 : (q + 1) ^ 3 = (q + 1) * (q + 1) * (q + 1) := by ring
  by_cases h1 : s ∣ q - 1
  ·
    have hB1 : B = 1 := ordProj_eq_one_of_not_dvd fun h2 =>
      false_of_dvd_sub_of_dvd_add hs hs2 hq1 h1 h2
    have hC1 : C = 1 := ordProj_eq_one_of_not_dvd fun h2 =>
      false_of_dvd_sub_of_dvd_sq hs hs2 hq1 h1 h2
    have hE1 : E = 1 := ordProj_eq_one_of_not_dvd fun h2 =>
      false_of_dvd_sub_of_dvd_e hs h1 h2
    have hD3 : D ≤ 3 := ordProj_d_le_three hs hsq hq1 h1
    rw [hB1, hC1, hE1, one_pow, one_pow, one_pow, mul_one, mul_one, mul_one]
    have h8 : 8 * A ^ 3 ≤ (q + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (hA2.trans (by omega : q - 1 ≤ q + 1)) 3
      rw [mul_pow] at this
      norm_num at this
      exact this
    calc A ^ a * D ^ d ≤ A ^ 3 * 3 :=
          Nat.mul_le_mul (hle3 (hpos _) ha) ((hle1 (hpos _) hd).trans hD3)
      _ ≤ 8 * A ^ 3 := by omega
      _ ≤ (q + 1) ^ 3 := h8
  have hA1 : A = 1 := ordProj_eq_one_of_not_dvd h1
  by_cases h2 : s ∣ q + 1
  ·
    have hC1 : C = 1 := ordProj_eq_one_of_not_dvd fun h3 =>
      false_of_dvd_add_of_dvd_sq hs hs2 hq1 h2 h3
    have hD1 : D = 1 := ordProj_eq_one_of_not_dvd fun h3 =>
      false_of_dvd_add_of_dvd_d hs h2 h3
    have hE3 : E ≤ 3 := ordProj_e_le_three hs hsq hq1 h2
    rw [hA1, hC1, hD1, one_pow, one_pow, one_pow, one_mul, mul_one, mul_one]
    have h8 : 8 * B ^ 3 ≤ (q + 1) ^ 3 := by
      have := Nat.pow_le_pow_left hB2 3
      rw [mul_pow] at this
      norm_num at this
      exact this
    calc B ^ b * E ^ e ≤ B ^ 3 * 3 :=
          Nat.mul_le_mul (hle3 (hpos _) hb) ((hle1 (hpos _) he).trans hE3)
      _ ≤ 8 * B ^ 3 := by omega
      _ ≤ (q + 1) ^ 3 := h8
  have hB1 : B = 1 := ordProj_eq_one_of_not_dvd h2
  rw [hA1, hB1, one_pow, one_pow, one_mul, one_mul]
  have hsq3 : q ^ 2 + q + 1 ≤ (q + 1) ^ 3 := by nlinarith
  by_cases h3 : s ∣ q ^ 2 + 1
  · have hD1 : D = 1 := ordProj_eq_one_of_not_dvd fun h4 =>
      false_of_dvd_sq_of_dvd_d hsq h3 h4
    have hE1 : E = 1 := ordProj_eq_one_of_not_dvd fun h4 =>
      false_of_dvd_sq_of_dvd_e hsq hq1 h3 h4
    rw [hD1, hE1, one_pow, one_pow, mul_one, mul_one]
    calc C ^ c ≤ C := hle1 (hpos _) hc
      _ ≤ q ^ 2 + 1 := hC
      _ ≤ (q + 1) ^ 3 := by omega
  have hC1 : C = 1 := ordProj_eq_one_of_not_dvd h3
  rw [hC1, one_pow, one_mul]
  by_cases h4 : s ∣ q ^ 2 + q + 1
  · have hE1 : E = 1 := ordProj_eq_one_of_not_dvd fun h5 =>
      false_of_dvd_d_of_dvd_e hs hs2 hsq hq1 h4 h5
    rw [hE1, one_pow, mul_one]
    exact (hle1 (hpos _) hd).trans (hD.trans hsq3)
  have hD1 : D = 1 := ordProj_eq_one_of_not_dvd h4
  rw [hD1, one_pow, one_mul]
  exact (hle1 (hpos _) he).trans (hE.trans (by omega))

theorem ordProj_l4_le (hq : 3 ≤ q) (hqo : Odd q) (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q) :
    ordProj[s] (q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)))) ≤ (q + 1) ^ 3 := by
  have hq1 : 1 ≤ q := by omega
  have hval : q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) = q ^ 6 *
      ((q - 1) ^ 3 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 1 * (q ^ 2 + q + 1) ^ 1 *
        (q ^ 2 - q + 1) ^ 0) := by
    zify [hq1, Nat.one_le_pow 2 q hq1, Nat.one_le_pow 3 q hq1, Nat.one_le_pow 4 q hq1]
    ring
  have hsQ : ¬ s ∣ q ^ 6 := fun h => hsq (hs.dvd_of_dvd_pow h)
  rw [hval, Nat.ordProj_mul s (by positivity) (cyc_ne_zero (by omega) _ _ _ _ _),
    ordProj_eq_one_of_not_dvd hsQ,
    one_mul]
  exact ordProj_cyc_le hq hqo hs hs2 hsq (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num)

theorem ordProj_u4_le (hq : 3 ≤ q) (hqo : Odd q) (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q) :
    ordProj[s] (q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)))) ≤ (q + 1) ^ 3 := by
  have hq1 : 1 ≤ q := by omega
  have hle : q ≤ q ^ 2 := by nlinarith
  have hval : q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) = q ^ 6 *
      ((q - 1) ^ 2 * (q + 1) ^ 3 * (q ^ 2 + 1) ^ 1 * (q ^ 2 + q + 1) ^ 0 *
        (q ^ 2 - q + 1) ^ 1) := by
    zify [hq1, hle, Nat.one_le_pow 2 q hq1, Nat.one_le_pow 4 q hq1]
    ring
  have hsQ : ¬ s ∣ q ^ 6 := fun h => hsq (hs.dvd_of_dvd_pow h)
  rw [hval, Nat.ordProj_mul s (by positivity) (cyc_ne_zero (by omega) _ _ _ _ _),
    ordProj_eq_one_of_not_dvd hsQ,
    one_mul]
  exact ordProj_cyc_le hq hqo hs hs2 hsq (by norm_num) le_rfl le_rfl (by norm_num) le_rfl

theorem ordProj_o7_le (hq : 3 ≤ q) (hqo : Odd q) (hs : s.Prime) (hs2 : s ≠ 2) (hsq : ¬ s ∣ q) :
    ordProj[s] (q ^ 9 * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1)))) ≤ (q + 1) ^ 3 := by
  have hq1 : 1 ≤ q := by omega
  have hle : q ≤ q ^ 2 := by nlinarith
  have hval : q ^ 9 * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) = q ^ 9 *
      ((q - 1) ^ 3 * (q + 1) ^ 3 * (q ^ 2 + 1) ^ 1 * (q ^ 2 + q + 1) ^ 1 *
        (q ^ 2 - q + 1) ^ 1) := by
    zify [hq1, hle, Nat.one_le_pow 2 q hq1, Nat.one_le_pow 4 q hq1, Nat.one_le_pow 6 q hq1]
    ring
  have hsQ : ¬ s ∣ q ^ 9 := fun h => hsq (hs.dvd_of_dvd_pow h)
  rw [hval, Nat.ordProj_mul s (by positivity) (cyc_ne_zero (by omega) _ _ _ _ _),
    ordProj_eq_one_of_not_dvd hsQ,
    one_mul]
  exact ordProj_cyc_le hq hqo hs hs2 hsq le_rfl le_rfl le_rfl le_rfl le_rfl

theorem four_mul_pow_nine_le_l4 (hq : 3 ≤ q) :
    4 * ((q + 1) ^ 3) ^ 3 ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ u + 3 := by omega
  zify [Nat.one_le_pow 2 _ h1, Nat.one_le_pow 3 _ h1, Nat.one_le_pow 4 _ h1]
  rw [← sub_nonneg]
  ring_nf
  positivity

theorem four_mul_pow_nine_le_u4 (hq : 3 ≤ q) :
    4 * ((q + 1) ^ 3) ^ 3 ≤ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ u + 3 := by omega
  zify [Nat.one_le_pow 2 _ h1, Nat.one_le_pow 4 _ h1]
  rw [← sub_nonneg]
  ring_nf
  positivity

theorem two_mul_pow_nine_le_o7 (hq : 3 ≤ q) :
    2 * ((q + 1) ^ 3) ^ 3 ≤ q ^ 9 * ((q ^ 2 - 1) * ((q ^ 4 - 1) * (q ^ 6 - 1))) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ u + 3 := by omega
  zify [Nat.one_le_pow 2 _ h1, Nat.one_le_pow 4 _ h1, Nat.one_le_pow 6 _ h1]
  rw [← sub_nonneg]
  ring_nf
  positivity

theorem two_mul_pow_six_le_sp4 (hq : 3 ≤ q) :
    2 * ((q + 1) ^ 2) ^ 3 ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 3 := ⟨q - 3, by omega⟩
  have h1 : 1 ≤ u + 3 := by omega
  zify [Nat.one_le_pow 2 _ h1, Nat.one_le_pow 4 _ h1]
  rw [← sub_nonneg]
  ring_nf
  positivity

end CFSG.ComponentClassification.HarrisLit.T1.RowLie
