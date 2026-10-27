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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BS4

open Matrix

variable {F : Type} [Field F]

theorem exists_eq_smul_add_smul {B M : Matrix (Fin 2) (Fin 2) F} (hB : ∀ c : F, B ≠ c • 1)
    (hM : M * B = B * M) : ∃ x y : F, M = x • 1 + y • B := by
  have e := fun i j => congrFun (congrFun hM i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  by_cases hb : B 0 1 = 0
  · by_cases hc : B 1 0 = 0
    · have had : B 0 0 ≠ B 1 1 := by
        intro h
        apply hB (B 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, h]
      have hd : B 0 0 - B 1 1 ≠ 0 := sub_ne_zero.mpr had
      have h01 : M 0 1 = 0 := by
        have : M 0 1 * (B 1 1 - B 0 0) = 0 := by
          linear_combination e01 + (M 1 1 - M 0 0) * hb
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd (by linear_combination -h) hd
      have h10 : M 1 0 = 0 := by
        have : M 1 0 * (B 0 0 - B 1 1) = 0 := by
          linear_combination e10 + (M 0 0 - M 1 1) * hc
        exact (mul_eq_zero.mp this).resolve_right hd
      obtain ⟨y, hy⟩ : ∃ y, y = (M 0 0 - M 1 1) / (B 0 0 - B 1 1) := ⟨_, rfl⟩
      have hyB : y * (B 0 0 - B 1 1) = M 0 0 - M 1 1 := by rw [hy]; field_simp
      refine ⟨M 0 0 - y * B 0 0, y, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp [hb, h01]
      · simp [hc, h10]
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        linear_combination hyB
    · have h01 : M 0 1 = 0 := by
        have : M 0 1 * B 1 0 = 0 := by linear_combination e00 + M 1 0 * hb
        exact (mul_eq_zero.mp this).resolve_right hc
      obtain ⟨y, hy⟩ : ∃ y, y = M 1 0 / B 1 0 := ⟨_, rfl⟩
      have hyc : y * B 1 0 = M 1 0 := by rw [hy]; field_simp
      have h11 : M 1 1 = M 0 0 - y * B 0 0 + y * B 1 1 := by
        have : (M 1 1 - (M 0 0 - y * B 0 0 + y * B 1 1)) * B 1 0 = 0 := by
          linear_combination e10 + (B 0 0 - B 1 1) * hyc
        have := (mul_eq_zero.mp this).resolve_right hc
        linear_combination this
      refine ⟨M 0 0 - y * B 0 0, y, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp
      · simp [hb, h01]
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul]
        simp [hyc]
      · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_eq, smul_eq_mul, mul_one]
        exact h11
  · obtain ⟨y, hy⟩ : ∃ y, y = M 0 1 / B 0 1 := ⟨_, rfl⟩
    have hyb : y * B 0 1 = M 0 1 := by rw [hy]; field_simp
    have h10 : M 1 0 = y * B 1 0 := by
      have : (M 1 0 - y * B 1 0) * B 0 1 = 0 := by
        linear_combination -e00 - B 1 0 * hyb
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
    have h11 : M 1 1 = M 0 0 - y * B 0 0 + y * B 1 1 := by
      have : (M 1 1 - (M 0 0 - y * B 0 0 + y * B 1 1)) * B 0 1 = 0 := by
        linear_combination -e01 + (B 0 0 - B 1 1) * hyb
      have := (mul_eq_zero.mp this).resolve_right hb
      linear_combination this
    refine ⟨M 0 0 - y * B 0 0, y, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      simp [hyb]
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      simp [h10]
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact h11

theorem comm_of_comm_nonscalar {B M N : Matrix (Fin 2) (Fin 2) F} (hB : ∀ c : F, B ≠ c • 1)
    (hM : M * B = B * M) (hN : N * B = B * N) : M * N = N * M := by
  obtain ⟨x, y, rfl⟩ := exists_eq_smul_add_smul hB hM
  obtain ⟨x', y', rfl⟩ := exists_eq_smul_add_smul hB hN
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_add, smul_smul]
  rw [mul_comm x' x, mul_comm y' x, mul_comm x' y, mul_comm y' y]
  abel

theorem eq_one_or_neg_one_of_sq (h2 : (2 : F) ≠ 0) {N : Matrix (Fin 2) (Fin 2) F}
    (hN : N * N = 1) (hdet : N.det = 1) : N = 1 ∨ N = -1 := by
  have e := fun i j => congrFun (congrFun hN i) j
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, Matrix.one_apply_ne,
    ne_eq, Fin.reduceEq, not_false_eq_true] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hdet
  have ht : N 0 0 + N 1 1 ≠ 0 := by
    intro h
    have : (2 : F) = 0 := by linear_combination -e00 - hdet + N 0 0 * h
    exact h2 this
  have h01 : N 0 1 = 0 := by
    have : N 0 1 * (N 0 0 + N 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right ht
  have h10 : N 1 0 = 0 := by
    have : N 1 0 * (N 0 0 + N 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right ht
  rw [h01, h10] at e00 e11 hdet
  have h0 : N 0 0 = N 1 1 := by
    have : (N 0 0 - N 1 1) * (N 0 0 + N 1 1) = 0 := by linear_combination e00 - e11
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ht)
  have hsq : (N 0 0 - 1) * (N 0 0 + 1) = 0 := by linear_combination e00
  rcases mul_eq_zero.mp hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;>
      first | linear_combination h | linear_combination h - h0
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;>
      first | linear_combination h | linear_combination h - h0

theorem ul_mul {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hN : N.toBlocks₂₁ = 0) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j
  have h0 : ∀ l, N (Sum.inr l) (Sum.inl j) = 0 := fun l => congrFun (congrFun hN l) j
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, h0]

theorem lr_mul {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hM : M.toBlocks₂₁ = 0) :
    (M * N).toBlocks₂₂ = M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  have h0 : ∀ l, M (Sum.inr i) (Sum.inl l) = 0 := fun l => congrFun (congrFun hM i) l
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, h0]

theorem ll_mul {M N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hM : M.toBlocks₂₁ = 0)
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₂₁ = 0 := by
  ext i j
  have h0 : ∀ l, M (Sum.inr i) (Sum.inl l) = 0 := fun l => congrFun (congrFun hM i) l
  have h1 : ∀ l, N (Sum.inr l) (Sum.inl j) = 0 := fun l => congrFun (congrFun hN l) j
  simp [Matrix.toBlocks₂₁, Matrix.mul_apply, Fintype.sum_sum_type, h0, h1]

theorem ul_transpose_mul_lr {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {μ : F}
    (hM : M.toBlocks₂₁ = 0) (hJ : Mᵀ * Matrix.fromBlocks 0 1 (-1) 0 * M =
      μ • Matrix.fromBlocks 0 1 (-1) 0) : M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = μ • 1 := by
  ext i j
  have h := congrFun (congrFun hJ (Sum.inl i)) (Sum.inr j)
  have h0 : ∀ k l, M (Sum.inr k) (Sum.inl l) = 0 := fun k l => congrFun (congrFun hM k) l
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, h0] at h
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply] at h ⊢
  convert h using 1

end BS4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
