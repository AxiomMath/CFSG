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

namespace CFSG.Semidihedral.FieldFactorOne

namespace Numerics

theorem le_of_modEq_four_mul_sub_one_of_neg {k : ℕ} (hk : 1 ≤ k) {a : ℤ}
    (h : a ≡ 4 * k - 1 [ZMOD 8 * k]) (ha : a < 0) : a ≤ -(4 * k) - 1 := by
  obtain ⟨t, ht⟩ := h.dvd
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have ht1 : 1 ≤ t := by
    by_contra! hlt
    nlinarith
  nlinarith

theorem le_of_modEq_one_of_pos {k : ℕ} (hk : 1 ≤ k) {a : ℤ} (h : a ≡ 1 [ZMOD 8 * k])
    (ha : 0 < a) (ha1 : a ≠ 1) : 8 * k + 1 ≤ a := by
  obtain ⟨t, ht⟩ := h.dvd
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have ht1 : t ≤ -1 := by
    by_contra! hlt
    have : 2 ≤ a := by omega
    nlinarith
  nlinarith

theorem add_ne_zero_of_modEq {k : ℕ} (hk : 1 ≤ k) {a₀ a₃ : ℤ} (h₀ : a₀ ≡ 1 [ZMOD 8 * k])
    (h₃ : a₃ ≡ 4 * k - 1 [ZMOD 8 * k]) : a₀ + a₃ ≠ 0 := by
  intro h0
  obtain ⟨t, ht⟩ := (h₀.add h₃).dvd
  have hk0 : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have h2 : (4 * (k : ℤ)) * (1 - 2 * t) = 0 := by linear_combination ht + h0
  rcases mul_eq_zero.mp h2 with h | h <;> omega

theorem odd_of_modEq_eight_mul {k : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD 8 * k]) (hb : Odd b) :
    Odd a := by
  obtain ⟨s, hs⟩ := h.dvd
  obtain ⟨r, hr⟩ := hb
  exact ⟨r - 4 * k * s, by linear_combination hr - hs⟩

theorem mul_eq_of_moment {q a₀ a₁ a₂ a₃ : ℤ} (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (ha₃ : a₃ ≠ 0) (h03 : a₀ + a₃ ≠ 0) (hsum : a₀ + a₁ + a₂ + a₃ = 0)
    (hrec : (1 : ℚ) / a₀ + q ^ 2 / a₁ + q ^ 2 / a₂ + 1 / a₃ = 0) :
    a₁ * a₂ = q ^ 2 * a₀ * a₃ := by
  have e₀ : (a₀ : ℚ) ≠ 0 := by exact_mod_cast ha₀
  have e₁ : (a₁ : ℚ) ≠ 0 := by exact_mod_cast ha₁
  have e₂ : (a₂ : ℚ) ≠ 0 := by exact_mod_cast ha₂
  have e₃ : (a₃ : ℚ) ≠ 0 := by exact_mod_cast ha₃
  have hq : ((a₁ * a₂ * a₃ + q ^ 2 * a₀ * a₂ * a₃ + q ^ 2 * a₀ * a₁ * a₃ + a₀ * a₁ * a₂ : ℤ) : ℚ)
      = 0 := by
    field_simp at hrec
    push_cast
    linear_combination hrec
  have hz : a₁ * a₂ * a₃ + q ^ 2 * a₀ * a₂ * a₃ + q ^ 2 * a₀ * a₁ * a₃ + a₀ * a₁ * a₂ = 0 := by
    exact_mod_cast hq
  have h2 : (a₀ + a₃) * (a₁ * a₂ - q ^ 2 * a₀ * a₃) = 0 := by
    linear_combination hz - q ^ 2 * a₀ * a₃ * hsum
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h h03
  · linarith

theorem quotient_relation_mul {q e a₀ a₁ a₂ a₃ : ℤ} (he : e = 1 ∨ e = -1)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0) (hP : a₁ * a₂ = q ^ 2 * a₀ * a₃) :
    (a₁ - e * q * a₀) ^ 2 * (q - e) * (a₀ * a₂ * (a₀ + a₂)) =
      (a₂ + e * q * a₀) ^ 2 * (q + e) * (a₀ * a₁ * (a₀ + a₁)) := by
  have hE : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain rfl : a₃ = -(a₀ + a₁ + a₂) := by linarith
  linear_combination (-a₀ * (a₀ * a₁ * e + a₀ * a₁ * q + a₀ * a₂ * e - a₀ * a₂ * q
      + 2 * a₁ * a₂ * e)) * hP + (-a₀ ^ 2 * q * (a₀ ^ 2 * a₁ * e * q + a₀ ^ 2 * a₁ * q ^ 2
      + a₀ ^ 2 * a₂ * e * q - a₀ ^ 2 * a₂ * q ^ 2 + a₀ * a₁ ^ 2 * e * q + a₀ * a₁ ^ 2 * q ^ 2
      + a₀ * a₂ ^ 2 * e * q - a₀ * a₂ ^ 2 * q ^ 2 + 2 * a₁ ^ 2 * a₂ - 2 * a₁ * a₂ ^ 2)) * hE

theorem first_quotient_dual {q e a₀ a₁ a₂ a₃ : ℤ} (he : e = 1 ∨ e = -1)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0) (hP : a₁ * a₂ = q ^ 2 * a₀ * a₃) :
    (a₁ - e * q * a₀) ^ 2 * (-1 * (a₃ * a₂ * (a₃ + a₂))) =
      (a₂ - e * q * a₃) ^ 2 * (a₀ * a₁ * (a₀ + a₁)) := by
  have hE : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain rfl : a₃ = -(a₀ + a₁ + a₂) := by linarith
  linear_combination (-(a₀ + a₁) ^ 2 * (a₁ + a₂)) * hP
    - (a₀ * q ^ 2 * (a₀ + a₁) ^ 2 * (a₁ + a₂) * (a₀ + a₁ + a₂)) * hE

theorem second_quotient_dual {q e a₀ a₁ a₂ a₃ : ℤ} (he : e = 1 ∨ e = -1)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0) (hP : a₁ * a₂ = q ^ 2 * a₀ * a₃) :
    (a₂ + e * q * a₀) ^ 2 * (-1 * (a₃ * a₁ * (a₃ + a₁))) =
      (a₁ - -e * q * a₃) ^ 2 * (a₀ * a₂ * (a₀ + a₂)) := by
  have hE : e ^ 2 = 1 := by rcases he with rfl | rfl <;> norm_num
  obtain rfl : a₃ = -(a₀ + a₁ + a₂) := by linarith
  linear_combination (-(a₀ + a₂) ^ 2 * (a₁ + a₂)) * hP
    - (a₀ * q ^ 2 * (a₀ + a₂) ^ 2 * (a₁ + a₂) * (a₀ + a₁ + a₂)) * hE

theorem lower_bound_of_eq_one {q a₁ a₂ a₃ : ℤ} (hq : 5 ≤ q) (h₂ : 1 < |a₂|)
    (hsum : 1 + a₁ + a₂ + a₃ = 0) (hprod : a₁ * a₂ = q ^ 2 * a₃) (h₃ : a₃ < 0 → a₃ ≤ -9) :
    2 * (a₁ * (1 + a₁)) < 5 * (a₁ - q) ^ 2 := by
  by_contra! hcon
  have hq2 : 0 < q ^ 2 := by positivity
  have ha₂0 : a₂ ≠ 0 := by
    rintro rfl
    simp at h₂
  have hpos : 0 < a₁ := by
    by_contra! h
    nlinarith
  have ha₂neg : a₂ < 0 := by
    rcases lt_or_gt_of_ne ha₂0 with h | h
    · exact h
    · have : 0 < q ^ 2 * a₃ := by rw [← hprod]; positivity
      have : 0 < a₃ := pos_of_mul_pos_right this hq2.le
      linarith
  have ha₃neg : a₃ < 0 := by
    have : q ^ 2 * a₃ < 0 := by rw [← hprod]; exact mul_neg_of_pos_of_neg hpos ha₂neg
    nlinarith
  have h9 := h₃ ha₃neg
  have hgt : -a₂ < a₁ := by linarith
  have hsq : 9 * q ^ 2 < a₁ ^ 2 := by nlinarith
  have h3q : 3 * q < a₁ := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr h3q) (by linarith : (0 : ℤ) < 3 * a₁ - q - 2)]

theorem lower_bound_of_eq_neg_one {q a₁ a₂ a₃ : ℤ} (hq : 5 ≤ q) (hqodd : Odd q)
    (h₁ : 1 < |a₁|) (h₂ : 1 < |a₂|) (ha₁ : Odd a₁) (hsum : 1 + a₁ + a₂ + a₃ = 0)
    (hprod : a₁ * a₂ = q ^ 2 * a₃) (h₃ : a₃ < 0 → a₃ ≤ -9) :
    2 * (a₁ * (1 + a₁)) < 5 * (a₁ + q) ^ 2 := by
  by_contra! hcon
  have hq2 : 0 < q ^ 2 := by positivity
  have ha₂0 : a₂ ≠ 0 := by
    rintro rfl
    simp at h₂
  have hneg : a₁ < 0 := by
    by_contra! h
    nlinarith
  rcases lt_or_gt_of_ne ha₂0 with ha₂neg | ha₂pos
  ·
    have hkey : (q ^ 2 + a₁) * (q ^ 2 + a₂) = q ^ 4 - q ^ 2 := by
      linear_combination hprod + q ^ 2 * hsum
    have hx : 1 < -a₁ := by rwa [abs_of_neg hneg] at h₁
    have hy : 1 < -a₂ := by rwa [abs_of_neg ha₂neg] at h₂
    have hbig : q ^ 2 < -a₁ := by
      by_contra! h
      have hqq : q ^ 2 < q ^ 4 := by nlinarith
      have hu : 0 < q ^ 2 + a₁ := by
        rcases (show (0 : ℤ) ≤ q ^ 2 + a₁ by linarith).lt_or_eq with h' | h'
        · exact h'
        · rw [← h'] at hkey
          nlinarith
      have hv : 0 < q ^ 2 + a₂ := by
        by_contra! hv
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hu.le hv]
      nlinarith [mul_le_mul (by linarith : q ^ 2 + a₁ ≤ q ^ 2 - 2)
        (by linarith : q ^ 2 + a₂ ≤ q ^ 2 - 2) hv.le (by nlinarith)]
    nlinarith [mul_pos_of_neg_of_neg hneg (by nlinarith : 3 * a₁ + 10 * q - 2 < 0)]
  ·
    have ha₃neg : a₃ < 0 := by
      have : q ^ 2 * a₃ < 0 := by rw [← hprod]; exact mul_neg_of_neg_of_pos hneg ha₂pos
      nlinarith
    have h9 := h₃ ha₃neg
    have hrel : a₁ ^ 2 + a₁ = -a₃ * (q ^ 2 + a₁) := by
      linear_combination a₁ * hsum - hprod
    by_cases hbig : q ^ 2 ≤ -a₁
    · nlinarith [mul_pos_of_neg_of_neg hneg (by nlinarith : 3 * a₁ + 10 * q - 2 < 0)]
    · push Not at hbig
      have h8 : 9 * q ^ 2 ≤ a₁ ^ 2 - 8 * a₁ := by
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -a₃ - 9)
          (by linarith : (0 : ℤ) ≤ q ^ 2 + a₁)]
      have hx3 : 3 * q - 3 ≤ -a₁ := by
        by_contra! h
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ 3 * q - 4 + a₁)
          (by linarith : (0 : ℤ) ≤ 3 * q + 4 - a₁)]
      have hx2 : 3 * q - 2 ≤ -a₁ := by
        obtain ⟨r, hr⟩ := hqodd
        obtain ⟨s, hs⟩ := ha₁
        omega
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -a₁ - (3 * q - 2))
        (by linarith : (0 : ℤ) ≤ -3 * a₁ - q - 4)]

theorem lower_bound_core {q e a₁ a₂ a₃ : ℤ} (hq : 5 ≤ q) (hqodd : Odd q) (he : e = 1 ∨ e = -1)
    (h₁ : 1 < |a₁|) (h₂ : 1 < |a₂|) (ha₁ : Odd a₁) (hsum : 1 + a₁ + a₂ + a₃ = 0)
    (hprod : a₁ * a₂ = q ^ 2 * a₃) (h₃ : a₃ < 0 → a₃ ≤ -9) :
    2 * (a₁ * (1 + a₁)) < 5 * (a₁ - e * q) ^ 2 := by
  rcases he with rfl | rfl
  · rw [one_mul]
    exact lower_bound_of_eq_one hq h₂ hsum hprod h₃
  · rw [neg_one_mul, sub_neg_eq_add]
    exact lower_bound_of_eq_neg_one hq hqodd h₁ h₂ ha₁ hsum hprod h₃

theorem pos_and_lt_of_two_fifths_lt {N D : ℤ} (hN : 0 ≤ N) (h : (2 / 5 : ℚ) < (N : ℚ) / D) :
    0 < D ∧ 2 * D < 5 * N := by
  have hD : 0 < D := by
    by_contra! hD
    have : (N : ℚ) / D ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hN) (by exact_mod_cast hD)
    linarith
  refine ⟨hD, ?_⟩
  rw [lt_div_iff₀ (by exact_mod_cast hD)] at h
  have : ((2 * D : ℤ) : ℚ) < ((5 * N : ℤ) : ℚ) := by push_cast; linarith
  exact_mod_cast this

theorem pos_and_lt_of_cross_eq {N D N' D' : ℤ} (hD : 0 < D) (h : 2 * D < 5 * N) (hN' : 0 ≤ N')
    (hD' : D' ≠ 0) (heq : N * D' = N' * D) : 0 < D' ∧ 2 * D' < 5 * N' := by
  have hN : 0 < N := by linarith
  have hD'pos : 0 < D' := by
    rcases lt_or_gt_of_ne hD' with h' | h'
    · nlinarith [mul_neg_of_pos_of_neg hN h']
    · exact h'
  have hN'pos : 0 < N' := by
    by_contra! h'
    nlinarith [mul_pos hN hD'pos]
  refine ⟨hD'pos, ?_⟩
  nlinarith [mul_lt_mul_of_pos_right h hN'pos]

theorem two_mul_abs_lt {q c σ a b : ℤ} (hq : 3 ≤ q) (hc : c = 1 ∨ c = -1) (hσ : σ = 1 ∨ σ = -1)
    (hb : b ≠ 0) (h9 : 0 < σ * a → 9 ≤ σ * a) (hD : 0 < σ * (a * b * (a + b)))
    (hN : 2 * (σ * (a * b * (a + b))) < 5 * (b - c * q * a) ^ 2) : 2 * |b| < 3 * q * |a| := by
  by_contra! hcon
  have hA : 0 ≤ |a| := abs_nonneg a
  have hB : 0 < |b| := abs_pos.mpr hb
  have hb2 : 0 < b ^ 2 := by positivity
  have hbsq : |b| ^ 2 = b ^ 2 := sq_abs b
  have h9a : 9 * |a| ≤ 2 * |b| := by nlinarith
  have hab : -(|a| * |b|) ≤ a * b := by rw [← abs_mul]; exact neg_abs_le _
  have hbab : 7 * b ^ 2 ≤ 9 * (b * (a + b)) := by
    nlinarith [mul_le_mul_of_nonneg_right h9a hB.le]
  have hbpos : 0 < b * (a + b) := by nlinarith
  have hσa : 0 < σ * a := by
    have h' : σ * (a * b * (a + b)) = (σ * a) * (b * (a + b)) := by ring
    rw [h'] at hD
    exact pos_of_mul_pos_left hD hbpos.le
  have hσabs : σ * a = |a| := by
    rcases hσ with rfl | rfl
    · rw [one_mul] at hσa ⊢
      exact (abs_of_pos hσa).symm
    · rw [neg_one_mul] at hσa ⊢
      exact (abs_of_neg (neg_pos.mp hσa)).symm
  have h9' := h9 hσa
  have hD14 : 14 * b ^ 2 ≤ 2 * (σ * (a * b * (a + b))) := by
    have h' : σ * (a * b * (a + b)) = (σ * a) * (b * (a + b)) := by ring
    rw [h']
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ σ * a - 9) hbpos.le]
  have habs : |b - c * q * a| ≤ |b| + q * |a| := by
    calc |b - c * q * a| ≤ |b| + |c * q * a| := abs_sub _ _
      _ = |b| + q * |a| := by
        rcases hc with rfl | rfl <;> simp [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < q)]
  have hN' : (b - c * q * a) ^ 2 ≤ (|b| + q * |a|) ^ 2 := by
    rw [← sq_abs (b - c * q * a)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have h53 : 3 * (|b| + q * |a|) ≤ 5 * |b| := by linarith
  have h25 : 9 * (|b| + q * |a|) ^ 2 ≤ 25 * b ^ 2 := by
    nlinarith [mul_le_mul h53 h53 (by positivity) (by positivity)]
  nlinarith

theorem lt_of_mul_eq_of_lt {q A₀ A₁ A₂ A₃ : ℤ} (hq : 3 ≤ q) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hP : A₁ * A₂ = q ^ 2 * A₀ * A₃) (h : 2 * A₂ < 3 * q * A₃) :
    2 * q * A₀ < 3 * A₁ ∧ 2 * A₀ < A₁ := by
  have hq0 : 0 < q := by linarith
  have h1 : 2 * q * A₀ < 3 * A₁ := by
    have := mul_lt_mul_of_pos_left h (by positivity : (0 : ℤ) < 2 * q * A₀)
    by_contra! h'
    nlinarith [mul_le_mul_of_nonneg_right h' hA₂.le]
  exact ⟨h1, by nlinarith⟩

theorem pos_of_two_mul_abs_lt {a₀ a₁ : ℤ} (h : 2 * |a₀| < |a₁|)
    (hD : 0 < a₀ * a₁ * (a₀ + a₁)) : 0 < a₀ := by
  have hab : -(|a₀| * |a₁|) ≤ a₀ * a₁ := by rw [← abs_mul]; exact neg_abs_le _
  have hA₁ : 0 < |a₁| := by linarith [abs_nonneg a₀]
  have h1 : 0 < a₁ * (a₀ + a₁) := by
    nlinarith [mul_lt_mul_of_pos_right h hA₁, sq_abs a₁, abs_nonneg a₀]
  have h' : a₀ * a₁ * (a₀ + a₁) = a₀ * (a₁ * (a₀ + a₁)) := by ring
  rw [h'] at hD
  exact pos_of_mul_pos_left hD h1.le

theorem sum_ne_zero_of_bounds {a₀ a₁ a₂ a₃ : ℤ} (ha₀ : 0 < a₀) (ha₃ : 0 < a₃)
    (hpos : 0 < a₁ * a₂) (b01 : 2 * a₀ < |a₁|) (b32 : 2 * a₃ < |a₂|) :
    a₀ + a₁ + a₂ + a₃ ≠ 0 := by
  have ha₁ : a₁ ≠ 0 := by
    rintro rfl
    simp at hpos
  rcases lt_or_gt_of_ne ha₁ with h1 | h1
  · have h2 : a₂ < 0 := neg_of_mul_pos_right hpos h1.le
    rw [abs_of_neg h1] at b01
    rw [abs_of_neg h2] at b32
    intro h
    linarith
  · have h2 : 0 < a₂ := pos_of_mul_pos_right hpos h1.le
    intro h
    linarith

theorem not_lt_of_ratio {q c a₀ b : ℤ} (hq : 3 ≤ q) (hc : c = 1 ∨ c = -1) (ha₀ : 17 ≤ a₀)
    (hb : 0 < b) (hratio : 2 * q * a₀ < 3 * b)
    (hN : 2 * (a₀ * b * (a₀ + b)) < 5 * (b - c * q * a₀) ^ 2) : False := by
  have hqa : 0 < q * a₀ := by positivity
  have hsq : (b - c * q * a₀) ^ 2 ≤ (b + q * a₀) ^ 2 := by
    rcases hc with rfl | rfl <;> nlinarith
  have h4 : 4 * (b + q * a₀) ^ 2 < 25 * b ^ 2 := by
    have h1 : 2 * (b + q * a₀) < 5 * b := by linarith
    nlinarith [mul_lt_mul'' h1 h1 (by positivity) (by positivity)]
  have hD : 17 * b ^ 2 ≤ a₀ * b * (a₀ + b) := by
    nlinarith [mul_le_mul_of_nonneg_right ha₀ (by positivity : (0 : ℤ) ≤ b * (a₀ + b))]
  nlinarith

end Numerics

open Numerics

theorem type_star_signed_degree_relations (q e : ℤ) (he : e = 1 ∨ e = -1) (k : ℕ) (hk : 2 ≤ k)
    (a₀ a₁ a₂ a₃ : ℤ) (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h01 : a₀ + a₁ ≠ 0) (h02 : a₀ + a₂ ≠ 0)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0)
    (hrec : (1 : ℚ) / a₀ + q ^ 2 / a₁ + q ^ 2 / a₂ + 1 / a₃ = 0)
    (hc₀ : a₀ ≡ 1 [ZMOD 8 * k]) (hc₃ : a₃ ≡ 4 * k - 1 [ZMOD 8 * k]) :
    a₁ * a₂ = q ^ 2 * a₀ * a₃ ∧ 0 < a₀ * a₁ * a₂ * a₃ ∧
      ((a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)) : ℚ) * (q - e) =
        ((a₂ + e * q * a₀) ^ 2 / (a₀ * a₂ * (a₀ + a₂)) : ℚ) * (q + e) := by
  have hP := mul_eq_of_moment ha₀ ha₁ ha₂ ha₃ (add_ne_zero_of_modEq (by omega) hc₀ hc₃) hsum hrec
  refine ⟨hP, ?_, ?_⟩
  · have hq : q ≠ 0 := by
      rintro rfl
      simp [ha₁, ha₂] at hP
    have h : a₀ * a₁ * a₂ * a₃ = q ^ 2 * (a₀ * a₃) ^ 2 := by
      linear_combination (a₀ * a₃) * hP
    rw [h]
    positivity
  · have hD₁ : (a₀ * a₁ * (a₀ + a₁) : ℚ) ≠ 0 := by
      have : a₀ * a₁ * (a₀ + a₁) ≠ 0 := by positivity
      exact_mod_cast this
    have hD₂ : (a₀ * a₂ * (a₀ + a₂) : ℚ) ≠ 0 := by
      have : a₀ * a₂ * (a₀ + a₂) ≠ 0 := by positivity
      exact_mod_cast this
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff hD₁ hD₂]
    have key : ((((a₁ - e * q * a₀) ^ 2 * (q - e) * (a₀ * a₂ * (a₀ + a₂)) : ℤ)) : ℚ) =
        (((a₂ + e * q * a₀) ^ 2 * (q + e) * (a₀ * a₁ * (a₀ + a₁)) : ℤ) : ℚ) := by
      rw [quotient_relation_mul he hsum hP]
    push_cast at key
    linear_combination key

theorem principal_quotient_bounds (p : ℕ) (hp : p.Prime) (hpodd : Odd p) (m : ℕ) (hm : 1 ≤ m)
    (q : ℤ) (hq : q = (p : ℤ) ^ m) (hq7 : 7 ≤ q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (k : ℕ) (hk : 2 ≤ k) (hkpow : ∃ j : ℕ, k = 2 ^ j) (hqe : e * q - 1 ≡ 2 * k [ZMOD 4 * k])
    (a₁ a₂ a₃ : ℤ) (h₁ : 1 < |a₁|) (h₂ : 1 < |a₂|) (h₃ : 1 < |a₃|)
    (hsum : 1 + a₁ + a₂ + a₃ = 0) (hprod : a₁ * a₂ = q ^ 2 * a₃)
    (hc₁ : a₁ ≡ 2 - e * q [ZMOD 8 * k]) (hc₂ : a₂ ≡ -(e * q) [ZMOD 8 * k])
    (hc₃ : a₃ ≡ 4 * k - 1 [ZMOD 8 * k]) :
    (2 / 5 : ℚ) < (a₁ - e * q) ^ 2 / (a₁ * (1 + a₁)) ∧
      (2 / 5 : ℚ) < (a₂ + e * q) ^ 2 / (a₂ * (1 + a₂)) := by
  have _ := hp; have _ := hm; have _ := hkpow; have _ := hqe; have _ := h₃
  have hqodd : Odd q := hq ▸ ((Int.odd_coe_nat p).mpr hpodd).pow
  have heq : Odd (e * q) := by rcases he with rfl | rfl <;> simpa using hqodd
  have ha₁ : Odd a₁ := odd_of_modEq_eight_mul hc₁ (by
    obtain ⟨r, hr⟩ := heq
    exact ⟨-r, by rw [hr]; ring⟩)
  have ha₂ : Odd a₂ := odd_of_modEq_eight_mul hc₂ heq.neg
  have h9 : a₃ < 0 → a₃ ≤ -9 := fun h => by
    have := le_of_modEq_four_mul_sub_one_of_neg (by omega) hc₃ h
    omega
  have hpos : ∀ a : ℤ, 1 < |a| → (0 : ℚ) < a * (1 + a) := fun a ha => by
    have : 0 < a * (1 + a) := by
      rcases lt_abs.mp ha with h | h <;> nlinarith
    exact_mod_cast this
  have I₁ := lower_bound_core (by linarith) hqodd he h₁ h₂ ha₁ hsum hprod h9
  have I₂ := lower_bound_core (e := -e) (by linarith) hqodd (by rcases he with rfl | rfl <;> simp)
    h₂ h₁ ha₂ (by linarith) (by rw [mul_comm]; exact hprod) h9
  constructor
  · rw [lt_div_iff₀ (hpos a₁ h₁)]
    have : ((2 * (a₁ * (1 + a₁)) : ℤ) : ℚ) < ((5 * (a₁ - e * q) ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast I₁
    push_cast at this
    linarith
  · rw [lt_div_iff₀ (hpos a₂ h₂)]
    have : ((2 * (a₂ * (1 + a₂)) : ℤ) : ℚ) < ((5 * (a₂ - -e * q) ^ 2 : ℤ) : ℚ) := by
      exact_mod_cast I₂
    push_cast at this
    nlinarith

theorem type_star_degree_one (q : ℤ) (hq : 3 ≤ q) (hqodd : Odd q) (e : ℤ) (he : e = 1 ∨ e = -1)
    (k : ℕ) (hk : 2 ≤ k) (hkpow : ∃ j : ℕ, k = 2 ^ j) (hqe : e * q - 1 ≡ 2 * k [ZMOD 4 * k])
    (a₀ a₁ a₂ a₃ : ℤ) (ha₀ : a₀ ≠ 0) (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (h01 : a₀ + a₁ ≠ 0) (h02 : a₀ + a₂ ≠ 0)
    (hsum : a₀ + a₁ + a₂ + a₃ = 0)
    (hrec : (1 : ℚ) / a₀ + q ^ 2 / a₁ + q ^ 2 / a₂ + 1 / a₃ = 0)
    (hc₀ : a₀ ≡ 1 [ZMOD 8 * k]) (hc₁ : a₁ ≡ 2 - e * q [ZMOD 8 * k])
    (hc₂ : a₂ ≡ -(e * q) [ZMOD 8 * k]) (hc₃ : a₃ ≡ 4 * k - 1 [ZMOD 8 * k])
    (hQ₁ : (2 / 5 : ℚ) < (a₁ - e * q * a₀) ^ 2 / (a₀ * a₁ * (a₀ + a₁)))
    (hQ₂ : (2 / 5 : ℚ) < (a₂ + e * q * a₀) ^ 2 / (a₀ * a₂ * (a₀ + a₂))) :
    a₀ = 1 := by
  have _ := hqodd; have _ := hkpow; have _ := hqe; have _ := hc₁; have _ := hc₂
  by_contra hne
  have hk1 : 1 ≤ k := by omega
  have hq0 : 0 < q := by linarith
  have hP := mul_eq_of_moment ha₀ ha₁ ha₂ ha₃ (add_ne_zero_of_modEq hk1 hc₀ hc₃) hsum hrec
  have h17 : 0 < a₀ → 17 ≤ a₀ := fun h => by
    have := le_of_modEq_one_of_pos hk1 hc₀ h hne
    omega
  have h9₀ : 0 < 1 * a₀ → 9 ≤ 1 * a₀ := fun h => by
    have := h17 (by rwa [one_mul] at h)
    omega
  have h9₃ : 0 < -1 * a₃ → 9 ≤ -1 * a₃ := fun h => by
    have := le_of_modEq_four_mul_sub_one_of_neg hk1 hc₃ (by omega)
    omega
  obtain ⟨hD₁, hN₁⟩ := pos_and_lt_of_two_fifths_lt (N := (a₁ - e * q * a₀) ^ 2)
    (D := a₀ * a₁ * (a₀ + a₁)) (sq_nonneg _) (by push_cast; exact hQ₁)
  obtain ⟨hD₂, hN₂⟩ := pos_and_lt_of_two_fifths_lt (N := (a₂ + e * q * a₀) ^ 2)
    (D := a₀ * a₂ * (a₀ + a₂)) (sq_nonneg _) (by push_cast; exact hQ₂)
  have h32 : a₃ + a₂ ≠ 0 := fun h => h01 (by linarith)
  have h31 : a₃ + a₁ ≠ 0 := fun h => h02 (by linarith)
  obtain ⟨hD₁', hN₁'⟩ := pos_and_lt_of_cross_eq hD₁ hN₁ (sq_nonneg _)
    (by rw [neg_one_mul, neg_ne_zero]; positivity) (first_quotient_dual he hsum hP)
  obtain ⟨hD₂', hN₂'⟩ := pos_and_lt_of_cross_eq hD₂ hN₂ (sq_nonneg _)
    (by rw [neg_one_mul, neg_ne_zero]; positivity) (second_quotient_dual he hsum hP)
  have he' : -e = 1 ∨ -e = -1 := by rcases he with rfl | rfl <;> simp
  have hsq₂ : (a₂ - -e * q * a₀) ^ 2 = (a₂ + e * q * a₀) ^ 2 := by ring
  have r01 : 2 * |a₁| < 3 * q * |a₀| :=
    two_mul_abs_lt hq he (Or.inl rfl) ha₁ h9₀ (by rwa [one_mul]) (by rwa [one_mul])
  have r02 : 2 * |a₂| < 3 * q * |a₀| :=
    two_mul_abs_lt hq he' (Or.inl rfl) ha₂ h9₀ (by rwa [one_mul]) (by rwa [one_mul, hsq₂])
  have r32 : 2 * |a₂| < 3 * q * |a₃| := two_mul_abs_lt hq he (Or.inr rfl) ha₂ h9₃ hD₁' hN₁'
  have r31 : 2 * |a₁| < 3 * q * |a₃| := two_mul_abs_lt hq he' (Or.inr rfl) ha₁ h9₃ hD₂' hN₂'
  have hPabs : |a₁| * |a₂| = q ^ 2 * |a₀| * |a₃| := by
    rw [← abs_mul, hP, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < q ^ 2)]
  have hA₀ : 0 < |a₀| := abs_pos.mpr ha₀
  have hA₁ : 0 < |a₁| := abs_pos.mpr ha₁
  have hA₂ : 0 < |a₂| := abs_pos.mpr ha₂
  have hA₃ : 0 < |a₃| := abs_pos.mpr ha₃
  obtain ⟨s01, b01⟩ := lt_of_mul_eq_of_lt hq hA₀ hA₂ hPabs r32
  obtain ⟨s02, -⟩ := lt_of_mul_eq_of_lt hq hA₀ hA₁ (by rw [mul_comm]; exact hPabs) r31
  obtain ⟨-, b32⟩ := lt_of_mul_eq_of_lt hq hA₃ hA₁ (by rw [mul_comm, hPabs]; ring) r01
  have ha₀pos := pos_of_two_mul_abs_lt b01 hD₁
  have ha₀17 := h17 ha₀pos
  rw [abs_of_pos ha₀pos] at s01 s02 b01
  have ha₃neg : a₃ < 0 := by
    rcases lt_or_gt_of_ne ha₃ with h | h
    · exact h
    · rw [abs_of_pos h] at b32
      exact (sum_ne_zero_of_bounds ha₀pos h (by rw [hP]; positivity) b01 b32 hsum).elim
  have hneg : a₁ * a₂ < 0 := by
    rw [hP]
    exact mul_neg_of_pos_of_neg (by positivity) ha₃neg
  rcases lt_or_gt_of_ne ha₁ with h1 | h1
  · have h2 : 0 < a₂ := pos_of_mul_neg_right hneg h1.le
    rw [abs_of_pos h2] at s02
    exact not_lt_of_ratio hq he' ha₀17 h2 s02 (by rw [hsq₂]; exact hN₂)
  · rw [abs_of_pos h1] at s01
    exact not_lt_of_ratio hq he ha₀17 h1 s01 hN₁

end CFSG.Semidihedral.FieldFactorOne
