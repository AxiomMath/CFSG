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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

open Matrix

variable {K : Type} [Field K]

theorem eq_zero_of_rel {g e e' : K} (h : g * e' = e * g) (hne : e' ≠ e) : g = 0 := by
  have h1 : g * (e' - e) = 0 := by linear_combination h
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hne)

theorem eq_of_rel {g e e' : K} (h : g * e' = e * g) (hg : g ≠ 0) : e' = e := by
  have h1 : g * (e' - e) = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hg)

theorem det_blockDiag4 (a b c d e f g h : K) :
    (!![a, b, 0, 0; c, d, 0, 0; 0, 0, e, f; 0, 0, g, h] : Matrix (Fin 4) (Fin 4) K).det =
      (a * d - b * c) * (e * h - f * g) := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem offBlock_zero (φ : K ≃+* K) {u v : K} (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hφu1 : φ u ≠ 1)
    (hφv1 : φ v ≠ 1) (G : Matrix (Fin 4) (Fin 4) K)
    (hd1 : G * !![φ u, 0, 0, 0; 0, φ v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![u, 0, 0, 0; 0, v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G) :
    G 0 2 = 0 ∧ G 0 3 = 0 ∧ G 1 2 = 0 ∧ G 1 3 = 0 ∧
      G 2 0 = 0 ∧ G 2 1 = 0 ∧ G 3 0 = 0 ∧ G 3 1 = 0 := by
  have e02 := congrFun (congrFun hd1 0) 2
  have e03 := congrFun (congrFun hd1 0) 3
  have e12 := congrFun (congrFun hd1 1) 2
  have e13 := congrFun (congrFun hd1 1) 3
  have e20 := congrFun (congrFun hd1 2) 0
  have e21 := congrFun (congrFun hd1 2) 1
  have e30 := congrFun (congrFun hd1 3) 0
  have e31 := congrFun (congrFun hd1 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e02 e03 e12 e13 e20 e21 e30 e31
  exact ⟨eq_zero_of_rel (e := u) (e' := 1) (by linear_combination e02) hu1.symm,
    eq_zero_of_rel (e := u) (e' := 1) (by linear_combination e03) hu1.symm,
    eq_zero_of_rel (e := v) (e' := 1) (by linear_combination e12) hv1.symm,
    eq_zero_of_rel (e := v) (e' := 1) (by linear_combination e13) hv1.symm,
    eq_zero_of_rel (e := 1) (e' := φ u) (by linear_combination e20) hφu1,
    eq_zero_of_rel (e := 1) (e' := φ v) (by linear_combination e21) hφv1,
    eq_zero_of_rel (e := 1) (e' := φ u) (by linear_combination e30) hφu1,
    eq_zero_of_rel (e := 1) (e' := φ v) (by linear_combination e31) hφv1⟩

theorem core4 (σ φ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {u v : K} (huv : u * v = 1)
    (hne : v ≠ u) (G : Matrix (Fin 4) (Fin 4) K) (hdet : G.det ≠ 0)
    (hd1 : G * !![φ u, 0, 0, 0; 0, φ v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![u, 0, 0, 0; 0, v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G)
    (hd2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, φ u, 0; 0, 0, 0, φ v] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, u, 0; 0, 0, 0, v] * G)
    (hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G)
    (hj2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] * G)
    (hA : ∀ a : K, ∃ b : K,
      G * !![φ a, φ b, 0, 0; -φ (σ b), φ (σ a), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
        !![a, b, 0, 0; -σ b, σ a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G) :
    (φ = RingEquiv.refl K ∧ ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      G = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) ∨
    (φ = σ ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      G = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) := by
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one huv
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, one_mul] at huv
    exact hne (huv.trans h.symm)
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, mul_one] at huv
    exact hne (h.trans huv.symm)
  have hφu1 : φ u ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
  have hφv1 : φ v ≠ 1 := fun h => hv1 (φ.injective (by rw [h, map_one]))
  have hφuv : φ u * φ v = 1 := by rw [← map_mul, huv, map_one]
  obtain ⟨g02, g03, g12, g13, g20, g21, g30, g31⟩ := offBlock_zero φ hu1 hv1 hφu1 hφv1 G hd1
  have b00 := congrFun (congrFun hd1 0) 0
  have b01 := congrFun (congrFun hd1 0) 1
  have b10 := congrFun (congrFun hd1 1) 0
  have b11 := congrFun (congrFun hd1 1) 1
  have c22 := congrFun (congrFun hd2 2) 2
  have c23 := congrFun (congrFun hd2 2) 3
  have c32 := congrFun (congrFun hd2 3) 2
  have c33 := congrFun (congrFun hd2 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at b00 b01 b10 b11 c22 c23 c32 c33
  have hG : G = !![G 0 0, G 0 1, 0, 0; G 1 0, G 1 1, 0, 0; 0, 0, G 2 2, G 2 3;
      0, 0, G 3 2, G 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g02, g03, g12, g13, g20, g21, g30, g31]
  have hdet' : (G 0 0 * G 1 1 - G 0 1 * G 1 0) * (G 2 2 * G 3 3 - G 2 3 * G 3 2) ≠ 0 := by
    rw [← det_blockDiag4, ← hG]
    exact hdet
  have hdet1 : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := left_ne_zero_of_mul hdet'
  have hdet2 : G 2 2 * G 3 3 - G 2 3 * G 3 2 ≠ 0 := right_ne_zero_of_mul hdet'
  by_cases h00 : G 0 0 = 0
  ·
    have hm : G 0 1 * G 1 0 ≠ 0 := by
      intro h
      apply hdet1
      rw [h00, h]
      ring
    have g01 : G 0 1 ≠ 0 := left_ne_zero_of_mul hm
    have g10 : G 1 0 ≠ 0 := right_ne_zero_of_mul hm
    have hφv : φ v = u := eq_of_rel b01 g01
    have hφu : φ u = v := eq_of_rel b10 g10
    have g11 : G 1 1 = 0 := eq_zero_of_rel b11 (by rw [hφv]; exact hne.symm)
    have g22 : G 2 2 = 0 := eq_zero_of_rel c22 (by rw [hφu]; exact hne)
    have g33 : G 3 3 = 0 := eq_zero_of_rel c33 (by rw [hφv]; exact hne.symm)
    have hn : G 2 3 * G 3 2 ≠ 0 := by
      intro h
      apply hdet2
      rw [g22, g33, h]
      ring
    have g23 : G 2 3 ≠ 0 := left_ne_zero_of_mul hn
    have g32 : G 3 2 ≠ 0 := right_ne_zero_of_mul hn
    have w1 : G 1 0 = -G 0 1 := by
      have e := congrFun (congrFun hj1 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, h00, g02, g03] at e
      linear_combination -e
    have w2 : G 3 2 = -G 2 3 := by
      have e := congrFun (congrFun hj2 2) 2
      simp [Matrix.mul_apply, Fin.sum_univ_four, g22, g20, g21] at e
      linear_combination -e
    have hφσ : ∀ a, φ (σ a) = a := by
      intro a
      obtain ⟨b, hb⟩ := hA a
      have e := congrFun (congrFun hb 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, h00, g11, g02, g03] at e
      exact eq_of_rel e g01
    refine Or.inr ⟨RingEquiv.ext fun c => ?_, G 0 1, G 2 3, g01, g23, ?_⟩
    · have := hφσ (σ c)
      rwa [hσσ] at this
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h00, g11, g22, g33, g02, g03, g12, g13, g20, g21, g30, g31, w1, w2]
  ·
    have hφu : φ u = u := eq_of_rel b00 h00
    have hφv : φ v = v := by
      have h1 : u * φ v = 1 := by rw [← hφu]; exact hφuv
      exact mul_left_cancel₀ hu0 (h1.trans huv.symm)
    have g01 : G 0 1 = 0 := eq_zero_of_rel b01 (by rw [hφv]; exact hne)
    have g10 : G 1 0 = 0 := eq_zero_of_rel b10 (by rw [hφu]; exact hne.symm)
    have g23 : G 2 3 = 0 := eq_zero_of_rel c23 (by rw [hφv]; exact hne)
    have g32 : G 3 2 = 0 := eq_zero_of_rel c32 (by rw [hφu]; exact hne.symm)
    have g11 : G 1 1 ≠ 0 := by
      intro h
      apply hdet1
      rw [h, g01]
      ring
    have g22 : G 2 2 ≠ 0 := by
      intro h
      apply hdet2
      rw [h, g23]
      ring
    have w1 : G 1 1 = G 0 0 := by
      have e := congrFun (congrFun hj1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g02, g03] at e
      linear_combination -e
    have w2 : G 3 3 = G 2 2 := by
      have e := congrFun (congrFun hj2 2) 3
      simp [Matrix.mul_apply, Fin.sum_univ_four, g23, g20, g21] at e
      linear_combination -e
    have hφ : ∀ a, φ a = a := by
      intro a
      obtain ⟨b, hb⟩ := hA a
      have e := congrFun (congrFun hb 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g10, g02, g03] at e
      exact eq_of_rel e h00
    refine Or.inl ⟨RingEquiv.ext hφ, G 0 0, G 2 2, h00, g22, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g01, g10, g23, g32, g02, g03, g12, g13, g20, g21, g30, g31, w1, w2]

theorem diag4_eq (a b c d : K) :
    (!![a, 0, 0, 0; 0, b, 0, 0; 0, 0, c, 0; 0, 0, 0, d] : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![a, b, c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sq_eq_of_scalar {s w : K} (hs : s ≠ 0) (hw : w ≠ 0) (c : K)
    (h : (!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] : Matrix (Fin 4) (Fin 4) K) *
        ((!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] : Matrix (Fin 4) (Fin 4) K) *
          !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] *
          !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹]) *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] =
      c • (!![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K)) :
    s * s = w * w := by
  have e11 := congrFun (congrFun h 1) 1
  have e02 := congrFun (congrFun h 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e11 e02
  have hc : c = 1 := by
    rw [← e11]
    field_simp
  rw [hc] at e02
  field_simp at e02
  linear_combination e02

theorem conj_scalar4 {s : K} (hs : s ≠ 0) (X : Matrix (Fin 4) (Fin 4) K) :
    (!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, s, 0; 0, 0, 0, s] : Matrix (Fin 4) (Fin 4) K) * X *
      !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, s⁻¹, 0; 0, 0, 0, s⁻¹] = X := by
  simp only [diag4_eq]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem conj_neg4 {s : K} (hs : s ≠ 0) (X : Matrix (Fin 4) (Fin 4) K) :
    (!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, -s, 0; 0, 0, 0, -s] : Matrix (Fin 4) (Fin 4) K) * X *
      !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, -s⁻¹, 0; 0, 0, 0, -s⁻¹] =
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * X *
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  simp only [diag4_eq]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem alpha_sq_matrix (φ : K ≃+* K) (hφφ : ∀ c, φ (φ c) = c)
    (G Gi X : Matrix (Fin 4) (Fin 4) K) :
    G * φ.mapMatrix (G * φ.mapMatrix X * Gi) * Gi =
      (G * φ.mapMatrix G) * X * (φ.mapMatrix Gi * Gi) := by
  have hmm : φ.mapMatrix (φ.mapMatrix X) = X := by
    ext i j
    simp [RingEquiv.mapMatrix_apply, hφφ]
  rw [map_mul, map_mul, hmm]
  simp only [Matrix.mul_assoc]

theorem inv_sq_matrix (φ : K ≃+* K) (G Gi : Matrix (Fin 4) (Fin 4) K) (hGiG : Gi * G = 1) :
    (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G) = 1 := by
  calc (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G)
      = φ.mapMatrix Gi * (Gi * G) * φ.mapMatrix G := by simp only [Matrix.mul_assoc]
    _ = φ.mapMatrix Gi * φ.mapMatrix G := by rw [hGiG, Matrix.mul_one]
    _ = φ.mapMatrix (Gi * G) := (map_mul _ _ _).symm
    _ = 1 := by rw [hGiG, map_one]

theorem inv_of_diag4 {s w : K} (hs : s ≠ 0) (hw : w ≠ 0) (Di : Matrix (Fin 4) (Fin 4) K)
    (h : Di * !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] = 1) :
    Di = !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
  have h2 : (!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] : Matrix (Fin 4) (Fin 4) K) *
      !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] = 1 := by
    simp only [diag4_eq]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  calc Di = Di * (!![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w] *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹]) := by rw [h2, Matrix.mul_one]
    _ = (Di * !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w]) *
        !![s⁻¹, 0, 0, 0; 0, s⁻¹, 0, 0; 0, 0, w⁻¹, 0; 0, 0, 0, w⁻¹] := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.one_mul]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
