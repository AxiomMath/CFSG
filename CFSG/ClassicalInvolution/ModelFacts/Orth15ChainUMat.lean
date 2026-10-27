module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU

open Matrix

variable {K : Type} [Field K]

theorem eq_zero_of_add_self (h2 : (2 : K) ≠ 0) {x : K} (hx : x + x = 0) : x = 0 := by
  have : (2 : K) * x = 0 := by linear_combination hx
  exact (mul_eq_zero.mp this).resolve_left h2

theorem block_of_comm_x (h2 : (2 : K) ≠ 0) (G : Matrix (Fin 3) (Fin 3) K)
    (h : G * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G) :
    G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 := by
  have e02 := congrFun (congrFun h 0) 2
  have e12 := congrFun (congrFun h 1) 2
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21
  exact ⟨eq_zero_of_add_self h2 (by linear_combination e02),
    eq_zero_of_add_self h2 (by linear_combination e12),
    eq_zero_of_add_self h2 (by linear_combination -e20),
    eq_zero_of_add_self h2 (by linear_combination -e21)⟩

theorem rot_of_comm_j (G : Matrix (Fin 3) (Fin 3) K)
    (h : G * !![0, 1, 0; -1, 0, 0; 0, 0, 1] = !![0, 1, 0; -1, 0, 0; 0, 0, 1] * G) :
    G 1 1 = G 0 0 ∧ G 1 0 = -G 0 1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e01
  exact ⟨by linear_combination -e01, by linear_combination -e00⟩

theorem off_of_comm_d {t s : K} (hts : s ≠ t) (G : Matrix (Fin 3) (Fin 3) K)
    (h : G * !![t, 0, 0; 0, s, 0; 0, 0, 1] = !![t, 0, 0; 0, s, 0; 0, 0, 1] * G) :
    G 0 1 = 0 ∧ G 1 0 = 0 := by
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e10
  have h1 : G 0 1 * (s - t) = 0 := by linear_combination e01
  have h2 : G 1 0 * (t - s) = 0 := by linear_combination e10
  exact ⟨(mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hts),
    (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hts.symm)⟩

theorem diag_of_comm_d {t s : K} (hts : s ≠ t) (G : Matrix (Fin 3) (Fin 3) K)
    (h : G * !![s, 0, 0; 0, t, 0; 0, 0, 1] = !![t, 0, 0; 0, s, 0; 0, 0, 1] * G) :
    G 0 0 = 0 ∧ G 1 1 = 0 := by
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e11
  have h1 : G 0 0 * (s - t) = 0 := by linear_combination e00
  have h2 : G 1 1 * (t - s) = 0 := by linear_combination e11
  exact ⟨(mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hts),
    (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hts.symm)⟩

theorem core_id (h2 : (2 : K) ≠ 0) {t s : K} (hts : s ≠ t) (G : Matrix (Fin 3) (Fin 3) K)
    (hx : G * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G)
    (hj : G * !![0, 1, 0; -1, 0, 0; 0, 0, 1] = !![0, 1, 0; -1, 0, 0; 0, 0, 1] * G)
    (hd : G * !![t, 0, 0; 0, s, 0; 0, 0, 1] = !![t, 0, 0; 0, s, 0; 0, 0, 1] * G)
    (hP : (G * G) * !![0, 0, 1; 0, -1, 0; 1, 0, 0] = !![0, 0, 1; 0, -1, 0; 1, 0, 0] * (G * G)) :
    ∃ a w : K, G = !![a, 0, 0; 0, a, 0; 0, 0, w] ∧ a * a = w * w := by
  obtain ⟨b02, b12, b20, b21⟩ := block_of_comm_x h2 G hx
  obtain ⟨r11, r10⟩ := rot_of_comm_j G hj
  obtain ⟨o01, o10⟩ := off_of_comm_d hts G hd
  have hG : G = !![G 0 0, 0, 0; 0, G 0 0, 0; 0, 0, G 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [b02, b12, b20, b21, r11, o01, o10]
  refine ⟨G 0 0, G 2 2, hG, ?_⟩
  have e02 := congrFun (congrFun hP 0) 2
  rw [hG] at e02
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02
  exact e02

theorem core_bar (h2 : (2 : K) ≠ 0) {t s : K} (hts : s ≠ t) (σ : K ≃+* K)
    (G : Matrix (Fin 3) (Fin 3) K)
    (hx : G * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G)
    (hj : G * !![0, 1, 0; -1, 0, 0; 0, 0, 1] = !![0, 1, 0; -1, 0, 0; 0, 0, 1] * G)
    (hd : G * !![s, 0, 0; 0, t, 0; 0, 0, 1] = !![t, 0, 0; 0, s, 0; 0, 0, 1] * G)
    (hu : (G.map σ)ᵀ * G = 1)
    (hP : (G * G.map σ) * !![0, 0, 1; 0, -1, 0; 1, 0, 0] =
      !![0, 0, 1; 0, -1, 0; 1, 0, 0] * (G * G.map σ)) : False := by
  obtain ⟨b02, b12, b20, b21⟩ := block_of_comm_x h2 G hx
  obtain ⟨r11, r10⟩ := rot_of_comm_j G hj
  obtain ⟨d00, d11⟩ := diag_of_comm_d hts G hd
  have hG : G = !![0, G 0 1, 0; -G 0 1, 0, 0; 0, 0, G 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [b02, b12, b20, b21, r11, r10, d00]
  obtain ⟨b, w, rfl⟩ : ∃ b w : K, G = !![0, b, 0; -b, 0, 0; 0, 0, w] := ⟨G 0 1, G 2 2, hG⟩
  have hmap : (!![0, b, 0; -b, 0, 0; 0, 0, w] : Matrix (Fin 3) (Fin 3) K).map σ =
      !![0, σ b, 0; -σ b, 0, 0; 0, 0, σ w] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmap] at hu hP
  have u00 := congrFun (congrFun hu 0) 0
  have u22 := congrFun (congrFun hu 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at u00 u22
  have e02 := congrFun (congrFun hP 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e02
  apply h2
  linear_combination -e02 - u00 - u22

end CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
