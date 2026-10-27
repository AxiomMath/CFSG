module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LyonsUnitaryFour

open Finset

theorem coord_sq_mul_le_of_orthogonal {ι : Type*} [DecidableEq ι] (B : Finset ι) {j : ι}
    (hj : j ∈ B) (x w : ι → ℝ) (hxw : ∑ k ∈ B, x k * w k = 0) :
    x j ^ 2 * ∑ k ∈ B, w k ^ 2 ≤ (∑ k ∈ B, x k ^ 2) * (∑ k ∈ B, w k ^ 2 - w j ^ 2) := by
  have hquad : ∀ l : ℝ, 0 ≤ (∑ k ∈ B, w k ^ 2 - w j ^ 2) * (l * l) + (-2 * (x j * w j)) * l +
      (∑ k ∈ B, x k ^ 2 - x j ^ 2) := by
    intro l
    have h1 : 0 ≤ ∑ k ∈ B.erase j, (x k + l * w k) ^ 2 := sum_nonneg fun k _ => sq_nonneg _
    have h2 := add_sum_erase B (fun k => (x k + l * w k) ^ 2) hj
    have h3 : ∑ k ∈ B, (x k + l * w k) ^ 2 = ∑ k ∈ B, x k ^ 2 + l ^ 2 * ∑ k ∈ B, w k ^ 2 := by
      have hexp : ∀ k, (x k + l * w k) ^ 2 = x k ^ 2 + l ^ 2 * w k ^ 2 + 2 * l * (x k * w k) := by
        intro k; ring
      simp only [hexp, sum_add_distrib, ← mul_sum, hxw, mul_zero, add_zero]
    nlinarith [h1, h2, h3]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

theorem sum_sq_linear_combination {ι κ : Type*} [Fintype κ] (B : Finset ι) (a : κ → ℝ)
    (v : κ → ι → ℝ) :
    ∑ k ∈ B, (∑ m, a m * v m k) ^ 2 = ∑ m, ∑ n, a m * a n * ∑ k ∈ B, v m k * v n k := by
  have hexp : ∀ k, (∑ m, a m * v m k) ^ 2 = ∑ m, ∑ n, a m * a n * (v m k * v n k) := by
    intro k
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => ?_
    ring
  simp only [hexp]
  rw [sum_comm]
  refine sum_congr rfl fun m _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun n _ => ?_
  rw [mul_sum]

theorem gram_row_contribution_le {ι κ : Type*} [DecidableEq ι] [Fintype κ] (B : Finset ι)
    {j : ι} (hj : j ∈ B) (v : κ → ι → ℝ) (w : ι → ℝ)
    (hw : ∀ m, ∑ k ∈ B, v m k * w k = 0) (a : κ → ℝ) :
    (∑ m, a m * v m j) ^ 2 * ∑ k ∈ B, w k ^ 2 ≤
      (∑ m, ∑ n, a m * a n * ∑ k ∈ B, v m k * v n k) * (∑ k ∈ B, w k ^ 2 - w j ^ 2) := by
  have hxw : ∑ k ∈ B, (∑ m, a m * v m k) * w k = 0 := by
    simp only [sum_mul]
    rw [sum_comm]
    simp only [mul_assoc, ← mul_sum, hw, mul_zero, sum_const_zero]
  rw [← sum_sq_linear_combination]
  exact coord_sq_mul_le_of_orthogonal B hj (fun k => ∑ m, a m * v m k) w hxw

theorem five_sum_sq_sub_sq_sum (d : Fin 5 → ℝ) :
    5 * ∑ i, d i ^ 2 - (∑ i, d i) ^ 2 =
      ∑ h, ∑ i ∈ univ.filter (fun i => h < i), (d h - d i) ^ 2 := by
  simp only [sum_filter, Fin.sum_univ_five]
  simp only [Fin.isValue, Fin.reduceLT, lt_self_iff_false, ite_true, ite_false]
  ring

theorem six_column_strict_contribution_lt {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (t w : ι → ℝ) (d : Fin 5 → ι → ℝ) (htt : ∑ k ∈ B, t k * t k = 16)
    (htd : ∀ i, ∑ k ∈ B, t k * d i k = 0)
    (hdd : ∀ i l, ∑ k ∈ B, d i k * d l k = if i = l then 16 else 12)
    (hwt : ∑ k ∈ B, t k * w k = 0) (hwd : ∀ i, ∑ k ∈ B, d i k * w k = 0) {j : ι} (hj : j ∈ B)
    (hwj : w j ≠ 0) :
    4 * t j ^ 2 + 16 * ∑ i, d i j ^ 2 - 3 * (∑ i, d i j) ^ 2 < 64 := by
  set s := ∑ i, d i j with hs
  set b : Fin 5 → ℝ := fun i => (d i j - 3 * s / 16) / 4 with hb
  set x : ι → ℝ := fun k => t j / 16 * t k + ∑ i, b i * d i k with hx
  have hxw : ∑ k ∈ B, x k * w k = 0 := by
    simp only [hx, add_mul, sum_add_distrib, sum_mul, mul_assoc, ← mul_sum, hwt, mul_zero,
      zero_add]
    rw [sum_comm]
    simp only [← mul_sum, hwd, mul_zero, sum_const_zero]
  have hbsum : ∑ i, b i = s / 64 := by
    simp only [hb, ← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, hs]
    ring
  have hbsq : ∑ i, b i * d i j = (∑ i, d i j ^ 2) / 4 - 3 * s ^ 2 / 64 := by
    have hterm : ∀ i, b i * d i j = d i j ^ 2 / 4 - 3 * s / 64 * d i j := by
      intro i; simp only [hb]; ring
    simp only [hterm, sum_sub_distrib, ← sum_div, ← mul_sum, ← hs]
    ring
  have hxj : x j = (4 * t j ^ 2 + 16 * ∑ i, d i j ^ 2 - 3 * s ^ 2) / 64 := by
    simp only [hx, hbsq]
    ring
  have hdcross : ∑ k ∈ B, (∑ i, b i * d i k) ^ 2 = 4 * ∑ i, b i ^ 2 + 12 * (∑ i, b i) ^ 2 := by
    rw [sum_sq_linear_combination]
    simp only [hdd]
    have : ∀ i : Fin 5, ∑ l, b i * b l * (if i = l then (16 : ℝ) else 12) =
        4 * b i ^ 2 + 12 * b i * ∑ l, b l := by
      intro i
      have hsplit : ∀ l, b i * b l * (if i = l then (16 : ℝ) else 12) =
          12 * b i * b l + (if i = l then 4 * b i * b l else 0) := by
        intro l
        split_ifs <;> ring
      simp only [hsplit, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum]
      ring
    simp only [this, sum_add_distrib, ← mul_sum, ← sum_mul]
    ring
  have htcross : ∑ k ∈ B, t k * ∑ i, b i * d i k = 0 := by
    simp only [mul_sum]
    rw [sum_comm]
    simp only [mul_left_comm (t _), ← mul_sum, htd, mul_zero, sum_const_zero]
  have hbsq' : ∑ i, b i ^ 2 = (∑ i, d i j ^ 2) / 16 - 51 * s ^ 2 / 4096 := by
    have : ∀ i, b i ^ 2 = (d i j ^ 2 - 3 * s / 8 * d i j + 9 * s ^ 2 / 256) / 16 := by
      intro i
      simp only [hb]
      ring
    simp only [this, ← sum_div, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      card_univ, Fintype.card_fin, ← hs]
    ring
  have hxx : ∑ k ∈ B, x k ^ 2 = (4 * t j ^ 2 + 16 * ∑ i, d i j ^ 2 - 3 * s ^ 2) / 64 := by
    have hexp : ∀ k, x k ^ 2 = (t j / 16) ^ 2 * (t k * t k) +
        2 * (t j / 16) * (t k * ∑ i, b i * d i k) + (∑ i, b i * d i k) ^ 2 := by
      intro k
      simp only [hx]
      ring
    simp only [hexp, sum_add_distrib, ← mul_sum, htt, htcross, hdcross, hbsum, hbsq']
    ring
  have hkey := coord_sq_mul_le_of_orthogonal B hj x w hxw
  rw [hxj, hxx] at hkey
  have hW : w j ^ 2 ≤ ∑ k ∈ B, w k ^ 2 :=
    single_le_sum (f := fun k => w k ^ 2) (fun k _ => sq_nonneg (w k)) hj
  have hwj2 : 0 < w j ^ 2 := by positivity
  set Q := 4 * t j ^ 2 + 16 * ∑ i, d i j ^ 2 - 3 * s ^ 2 with hQ
  by_contra hcon
  replace hcon := not_lt.mp hcon
  have hQpos : 0 < Q / 64 := by linarith
  have h1 : Q / 64 * ∑ k ∈ B, w k ^ 2 ≤ ∑ k ∈ B, w k ^ 2 - w j ^ 2 := by
    have := hkey
    rw [sq] at this
    nlinarith [hkey, hQpos]
  nlinarith [h1, hW, hwj2]

theorem six_column_strict_row_contribution {ι : Type*} [DecidableEq ι] (B : Finset ι)
    (t w : ι → ℝ) (d : Fin 5 → ι → ℝ) (htt : ∑ k ∈ B, t k * t k = 16)
    (htd : ∀ i, ∑ k ∈ B, t k * d i k = 0)
    (hdd : ∀ i l, ∑ k ∈ B, d i k * d l k = if i = l then 16 else 12)
    (hwt : ∑ k ∈ B, t k * w k = 0) (hwd : ∀ i, ∑ k ∈ B, d i k * w k = 0) {j : ι} (hj : j ∈ B)
    (hwj : w j ≠ 0) :
    4 * t j ^ 2 + ∑ i, d i j ^ 2 +
      3 * ∑ h, ∑ i ∈ univ.filter (fun i => h < i), (d h j - d i j) ^ 2 < 64 := by
  have h := six_column_strict_contribution_lt B t w d htt htd hdd hwt hwd hj hwj
  rw [← five_sum_sq_sub_sq_sum (fun i => d i j)]
  linarith

end CFSG.LyonsUnitaryFour
