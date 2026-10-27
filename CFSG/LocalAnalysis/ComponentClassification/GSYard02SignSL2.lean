module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Data.Nat.Totient
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

variable {F : Type} [Field F]

theorem matrix_eq_smul_one_of_commute_sl2 (M : Matrix (Fin 2) (Fin 2) F)
    (hM : ∀ A : Matrix (Fin 2) (Fin 2) F, A.det = 1 → A * M = M * A) :
    ∃ c : F, M = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have h1 := hM !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
  have h2 := hM !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])
  have hA := congrFun (congrFun h1 0) 0
  have hB := congrFun (congrFun h1 0) 1
  have hC := congrFun (congrFun h2 0) 0
  have hD := congrFun (congrFun h2 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hA hB hC hD
  have hM10 : M 1 0 = 0 := by first | linear_combination hA | linear_combination -hA
  have hM11 : M 1 1 = M 0 0 := by first | linear_combination hB | linear_combination -hB
  have hM01 : M 0 1 = 0 := by first | linear_combination hC | linear_combination -hC
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, hM10, hM11, hM01]

theorem neg_one_of_sq_eq_one_sl2 (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F}
    (hdet : A.det = 1) (hsq : A * A = 1) (hne : A ≠ 1) : A = -1 := by
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  have e11 := congrFun (congrFun hsq 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  by_cases hps : A 0 0 + A 1 1 = 0
  · exfalso
    apply h2
    first
      | linear_combination -e00 - hdet + (A 0 0) * hps
      | linear_combination e00 - hdet + (A 0 0) * hps
      | linear_combination -e00 + hdet + (A 0 0) * hps
      | linear_combination e00 + hdet + (A 0 0) * hps
  · have hA01 : A 0 1 = 0 := by
      have h : A 0 1 * (A 0 0 + A 1 1) = 0 := by
        first | linear_combination e01 | linear_combination -e01
      exact (mul_eq_zero.mp h).resolve_right hps
    have hA10 : A 1 0 = 0 := by
      have h : A 1 0 * (A 0 0 + A 1 1) = 0 := by
        first | linear_combination e10 | linear_combination -e10
      exact (mul_eq_zero.mp h).resolve_right hps
    rw [hA01, hA10] at e00 e11 hdet
    have hsq00 : A 0 0 * A 0 0 = 1 := by
      first | linear_combination e00 | linear_combination -e00
    have hdiag : A 1 1 = A 0 0 := by
      have h0 : A 0 0 ≠ 0 := by
        intro h0
        rw [h0] at hsq00
        norm_num at hsq00
      have h : A 0 0 * (A 1 1 - A 0 0) = 0 := by
        first | linear_combination hdet - hsq00 | linear_combination hsq00 - hdet
      have h' := (mul_eq_zero.mp h).resolve_left h0
      linear_combination h'
    have hp : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination hsq00
    rcases mul_eq_zero.mp hp with h1 | h1
    · exfalso
      apply hne
      have hp1 : A 0 0 = 1 := by linear_combination h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA01, hA10, hdiag, hp1]
    · have hp2 : A 0 0 = -1 := by linear_combination h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA01, hA10, hdiag, hp2]

theorem isSquare_det_of_commute_of_sq_eq_neg_one (h2 : (2 : F) ≠ 0)
    {a h : Matrix (Fin 2) (Fin 2) F} (ha : a.det = 1) (ha2 : a * a = -1)
    (hh : ∃ c : F, h * h = c • (1 : Matrix (Fin 2) (Fin 2) F)) (hc : h * a = a * h) :
    IsSquare h.det := by
  obtain ⟨c, hc2⟩ := hh
  rw [Matrix.det_fin_two] at ha ⊢
  have a00 := congrFun (congrFun ha2 0) 0
  have a01 := congrFun (congrFun ha2 0) 1
  have a10 := congrFun (congrFun ha2 1) 0
  have a11 := congrFun (congrFun ha2 1) 1
  have h00 := congrFun (congrFun hc2 0) 0
  have h01 := congrFun (congrFun hc2 0) 1
  have h10 := congrFun (congrFun hc2 1) 0
  have h11 := congrFun (congrFun hc2 1) 1
  have c00 := congrFun (congrFun hc 0) 0
  have c01 := congrFun (congrFun hc 0) 1
  have c10 := congrFun (congrFun hc 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a00 a01 a10 a11 h00 h01 h10 h11 c00 c01 c10
  generalize a 0 0 = p at *
  generalize a 0 1 = q at *
  generalize a 1 0 = r at *
  generalize a 1 1 = s at *
  generalize h 0 0 = x at *
  generalize h 0 1 = y at *
  generalize h 1 0 = u at *
  generalize h 1 1 = v at *
  have hps : p + s = 0 := by
    by_contra hne
    have hq : q = 0 := by
      have : q * (p + s) = 0 := by first | linear_combination a01 | linear_combination -a01
      exact (mul_eq_zero.mp this).resolve_right hne
    have hr : r = 0 := by
      have : r * (p + s) = 0 := by first | linear_combination a10 | linear_combination -a10
      exact (mul_eq_zero.mp this).resolve_right hne
    have hps' : p * s = 1 := by
      rw [hq, hr] at ha
      first | linear_combination ha | linear_combination -ha
    have hp2 : p * p = -1 := by
      rw [hq, hr] at a00
      first | linear_combination a00 | linear_combination -a00
    have hp0 : p ≠ 0 := by
      intro h0
      rw [h0] at hp2
      norm_num at hp2
    have : p * (p + s) = 0 := by linear_combination hp2 + hps'
    exact hne ((mul_eq_zero.mp this).resolve_left hp0)
  have hqr : q * r = -1 - p * p := by
    first | linear_combination a00 | linear_combination -a00
  have K2 : q * (x - v) = y * (p - s) := by
    first | linear_combination c01 | linear_combination -c01
  have K3 : r * (x - v) = u * (p - s) := by
    first | linear_combination c10 | linear_combination -c10
  have E1 : y * r = q * u := by
    first | linear_combination c00 | linear_combination -c00
  have H1 : y * (x + v) = 0 := by
    first | linear_combination h01 | linear_combination -h01
  have H2 : u * (x + v) = 0 := by
    first | linear_combination h10 | linear_combination -h10
  have H3 : x * x = v * v := by
    first | linear_combination h00 - h11 | linear_combination h11 - h00
  by_cases hxv : x + v = 0
  ·
    have hv : v = -x := by linear_combination hxv
    have K2' : q * x = p * y := by
      have : (2 : F) * (q * x - p * y) = 0 := by
        linear_combination K2 + q * hxv - y * hps
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
    have K3' : r * x = p * u := by
      have : (2 : F) * (r * x - p * u) = 0 := by
        linear_combination K3 + r * hxv - u * hps
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
    by_cases hp0 : p = 0
    ·
      have hqr' : q * r = -1 := by rw [hp0] at hqr; linear_combination hqr
      have hq0 : q ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hqr'
        exact one_ne_zero (neg_eq_zero.mp hqr'.symm)
      have hx0 : x = 0 := by
        have : q * x = 0 := by linear_combination K2' + y * hp0
        exact (mul_eq_zero.mp this).resolve_left hq0
      have hv0 : v = 0 := by linear_combination hxv - hx0
      have hyG : y + q * q * u = 0 := by
        linear_combination y * hqr' - q * E1
      refine ⟨q * u, ?_⟩
      linear_combination v * hx0 - u * hyG
    ·
      have hI : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0
      have hy : y = q * x * p⁻¹ := by linear_combination (-y) * hI - p⁻¹ * K2'
      have hu : u = r * x * p⁻¹ := by linear_combination (-u) * hI - p⁻¹ * K3'
      have hv' : v = -x := hv
      refine ⟨x * p⁻¹, ?_⟩
      rw [hy, hu, hv']
      linear_combination (-(x ^ 2 * p⁻¹ ^ 2)) * a00 + (x ^ 2 * (p * p⁻¹ + 1)) * hI
  ·
    have hy0 : y = 0 := (mul_eq_zero.mp H1).resolve_right hxv
    have hu0 : u = 0 := (mul_eq_zero.mp H2).resolve_right hxv
    have hxv' : (x - v) * (x + v) = 0 := by linear_combination H3
    have hxv'' : x - v = 0 := (mul_eq_zero.mp hxv').resolve_right hxv
    refine ⟨x, ?_⟩
    rw [hy0, hu0]
    linear_combination (-x) * hxv''

end CFSG.ComponentClassification.Sol76.Sig.GSYard02
