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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19K

variable {F : Type} [Field F]

@[expose] def IsBlockScalar (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 0 = M 1 1

@[expose] def IsBlockDiag (G : Matrix (Fin 3) (Fin 3) F) : Prop :=
  G 0 2 = 0 ∧ G 1 2 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0

theorem isBlockScalar_of_commute_transvections (M : Matrix (Fin 3) (Fin 3) F)
    (h1 : M * !![1, 1, 0; 0, 1, 0; 0, 0, 1] = !![1, 1, 0; 0, 1, 0; 0, 0, 1] * M)
    (h2 : M * !![1, 0, 0; 1, 1, 0; 0, 0, 1] = !![1, 0, 0; 1, 1, 0; 0, 0, 1] * M) :
    IsBlockScalar M := by
  have e := fun i j => congrFun (congrFun h1 i) j
  have e' := fun i j => congrFun (congrFun h2 i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e e'
  have a01 := e 0 1
  have a02 := e 0 2
  have a11 := e 1 1
  have a21 := e 2 1
  have b11 := e' 1 1
  have b12 := e' 1 2
  have b20 := e' 2 0
  simp at a01 a02 a11 a21 b11 b12 b20
  exact ⟨b11, b12, a11, a02, a21, b20, by linear_combination a01⟩

theorem isBlockDiag_of_commute_negBlock (h2 : (2 : F) ≠ 0) (G : Matrix (Fin 3) (Fin 3) F)
    (h : G * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * G) :
    IsBlockDiag G := by
  have e := fun i j => congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e
  have c02 := e 0 2
  have c12 := e 1 2
  have c20 := e 2 0
  have c21 := e 2 1
  simp at c02 c12 c20 c21
  have k : ∀ x : F, x = -x → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  exact ⟨k _ c02, k _ c12, k _ (by linear_combination -c20), k _ (by linear_combination -c21)⟩

theorem isBlockScalar_of_commute_unitary (h2 : (2 : F) ≠ 0) {v w : F} (hvw : v ≠ w)
    (M : Matrix (Fin 3) (Fin 3) F)
    (hz : M * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * M)
    (hd : M * !![v, 0, 0; 0, w, 0; 0, 0, 1] = !![v, 0, 0; 0, w, 0; 0, 0, 1] * M)
    (hj : M * !![0, 1, 0; -1, 0, 0; 0, 0, 1] = !![0, 1, 0; -1, 0, 0; 0, 0, 1] * M) :
    IsBlockScalar M := by
  obtain ⟨h02, h12, h20, h21⟩ := isBlockDiag_of_commute_negBlock h2 M hz
  have e := fun i j => congrFun (congrFun hd i) j
  have e' := fun i j => congrFun (congrFun hj i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three] at e e'
  have d01 := e 0 1
  have d10 := e 1 0
  have j01 := e' 0 1
  simp at d01 d10 j01
  have hvw' : w - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvw)
  have k01 : M 0 1 = 0 := by
    have : M 0 1 * (w - v) = 0 := by linear_combination d01
    exact (mul_eq_zero.mp this).resolve_right hvw'
  have k10 : M 1 0 = 0 := by
    have : M 1 0 * (w - v) = 0 := by linear_combination -d10
    exact (mul_eq_zero.mp this).resolve_right hvw'
  exact ⟨k01, h02, k10, h12, h20, h21, j01⟩

theorem commute_of_isBlockDiag {G M : Matrix (Fin 3) (Fin 3) F} (hG : IsBlockDiag G)
    (hM : IsBlockScalar M) : G * M = M * G := by
  obtain ⟨g02, g12, g20, g21⟩ := hG
  obtain ⟨m01, m02, m10, m12, m20, m21, m00⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, g02, g12, g20, g21, m01, m02, m10, m12, m20,
      m21, m00, mul_comm]

theorem transpose_eq_of_isBlockScalar {M : Matrix (Fin 3) (Fin 3) F} (hM : IsBlockScalar M) :
    M.transpose = M := by
  obtain ⟨m01, m02, m10, m12, m20, m21, -⟩ := hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m12, m20, m21]

theorem div_pow_three_eq {d s : F} (hs : s ≠ 0) (h : d ^ 2 = s ^ 3) : (d / s) ^ 3 = d := by
  rw [div_pow, div_eq_iff (pow_ne_zero 3 hs), ← h]
  ring

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
