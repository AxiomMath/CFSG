module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3OuterUniAlg

open Matrix Polynomial

variable {F : Type} [Field F]

theorem poly_unit_aeval (C : Matrix (Fin 3) (Fin 3) F) (hc4 : C * C * (C * C) = 1) (x y : F)
    (hxy : x ^ 2 + y ^ 2 = -1) :
    aeval C (Polynomial.C (-x - 1) + Polynomial.C y * X + Polynomial.C (x - 1) * X ^ 2 -
        Polynomial.C y * X ^ 3 : F[X]) *
      aeval C (Polynomial.C (x - 1) + Polynomial.C y * X + Polynomial.C (-x - 1) * X ^ 2 -
        Polynomial.C y * X ^ 3 : F[X]) = (4 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have key : (Polynomial.C (-x - 1) + Polynomial.C y * X + Polynomial.C (x - 1) * X ^ 2 -
        Polynomial.C y * X ^ 3 : F[X]) *
      (Polynomial.C (x - 1) + Polynomial.C y * X + Polynomial.C (-x - 1) * X ^ 2 -
        Polynomial.C y * X ^ 3 : F[X]) =
      4 + (X ^ 4 - 1) * (Polynomial.C (1 - x ^ 2 - 2 * y ^ 2) + Polynomial.C (2 * y) * X +
        Polynomial.C (y ^ 2) * X ^ 2) := by
    have e0 : Polynomial.C (x ^ 2 + y ^ 2 + 1) = (0 : F[X]) := by
      rw [show x ^ 2 + y ^ 2 + 1 = 0 by linear_combination hxy]; simp
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, map_one, map_ofNat] at e0 ⊢
    linear_combination (2 * (X ^ 2 - 1)) * e0
  rw [← map_mul, key]
  have h4 : C ^ 4 = 1 := by rw [show C ^ 4 = C * C * (C * C) by noncomm_ring]; exact hc4
  simp [h4]
  rw [show (4 : F[X]) = Polynomial.C (4 : F) from (map_ofNat Polynomial.C 4).symm, aeval_C,
    Algebra.algebraMap_eq_smul_one]

theorem poly_unit (C : Matrix (Fin 3) (Fin 3) F) (hc4 : C * C * (C * C) = 1) (x y : F)
    (hxy : x ^ 2 + y ^ 2 = -1) :
    ((-x - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + y • C + (x - 1) • (C * C) - y • (C * C * C)) *
      ((x - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + y • C + (-x - 1) • (C * C) - y • (C * C * C)) =
        (4 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have := poly_unit_aeval C hc4 x y hxy
  simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_sub, aeval_X, aeval_C,
    map_pow, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at this
  convert this using 2 <;> simp [pow_succ, mul_assoc]

@[expose] noncomputable def PsiHom (A Ai : Matrix (Fin 3) (Fin 3) F) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) (φ : F ≃+* F) : Matrix (Fin 3) (Fin 3) F →+* Matrix (Fin 3) (Fin 3) F where
  toFun M := A * M.map φ * Ai
  map_one' := by simp [h1]
  map_mul' M N := by
    calc A * (M * N).map φ * Ai = A * (M.map φ * N.map φ) * Ai := by rw [Matrix.map_mul]
      _ = (A * M.map φ * Ai) * (A * N.map φ * Ai) := by
        calc A * (M.map φ * N.map φ) * Ai = A * M.map φ * (Ai * A) * N.map φ * Ai := by
              rw [h2, Matrix.mul_one]; noncomm_ring
          _ = (A * M.map φ * Ai) * (A * N.map φ * Ai) := by noncomm_ring
  map_zero' := by simp
  map_add' M N := by simp [Matrix.map_add, Matrix.mul_add, Matrix.add_mul]

theorem PsiHom_apply (A Ai : Matrix (Fin 3) (Fin 3) F) (h1 : A * Ai = 1) (h2 : Ai * A = 1)
    (φ : F ≃+* F) (M : Matrix (Fin 3) (Fin 3) F) : PsiHom A Ai h1 h2 φ M = A * M.map φ * Ai := rfl

theorem PsiHom_smul (A Ai : Matrix (Fin 3) (Fin 3) F) (h1 : A * Ai = 1) (h2 : Ai * A = 1)
    (φ : F ≃+* F) (a : F) (M : Matrix (Fin 3) (Fin 3) F) :
    PsiHom A Ai h1 h2 φ (a • M) = φ a • PsiHom A Ai h1 h2 φ M := by
  simp only [PsiHom_apply, Matrix.map_smul' _ _ _ (φ.map_mul), Matrix.mul_smul, Matrix.smul_mul]

theorem mu_alg (h2 : (2 : F) ≠ 0) (φ : F ≃+* F) (A Ai C : Matrix (Fin 3) (Fin 3) F)
    (h1 : A * Ai = 1) (h2' : Ai * A = 1) (hAC : A * C.map φ * Ai = C)
    (hCu : (C.map φ)ᵀ * C = 1) (hc4 : C * C * (C * C) = 1) (x y : F) (hx : φ x = -x)
    (hy : φ y = -y) (hxy : x ^ 2 + y ^ 2 = -1) :
    ∃ K : Matrix (Fin 3) (Fin 3) F, A * K.map φ * Ai = (C * C) * K ∧ (K.map φ)ᵀ * K = 1 := by
  set Q : Matrix (Fin 3) (Fin 3) F :=
    (x - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + y • C + (-x - 1) • (C * C) - y • (C * C * C) with hQ
  have hφ2 : φ ((2 : F)⁻¹) = (2 : F)⁻¹ := by rw [map_inv₀, map_ofNat]
  have hφ1x : φ (x - 1) = -x - 1 := by rw [map_sub, map_one, hx]
  have hφ2x : φ (-x - 1) = x - 1 := by rw [map_sub, map_neg, map_one, hx, neg_neg]
  have hC5 : C * C * (C * C * C) = C := by
    calc C * C * (C * C * C) = (C * C * (C * C)) * C := by noncomm_ring
      _ = C := by rw [hc4, one_mul]
  have hC6 : C * C * C * (C * C * C) = C * C := by
    calc C * C * C * (C * C * C) = (C * C) * (C * C * (C * C)) := by noncomm_ring
      _ = C * C := by rw [hc4, mul_one]
  have hC5b : C * C * C * (C * C) = C := by
    calc C * C * C * (C * C) = (C * C * (C * C)) * C := by noncomm_ring
      _ = C := by rw [hc4, one_mul]
  refine ⟨(2 : F)⁻¹ • Q, ?_, ?_⟩
  · have hΨ : A * ((2 : F)⁻¹ • Q).map φ * Ai = PsiHom A Ai h1 h2' φ ((2 : F)⁻¹ • Q) := rfl
    have hΨC : PsiHom A Ai h1 h2' φ C = C := hAC
    rw [hΨ, PsiHom_smul, hφ2, hQ]
    simp only [map_add, map_sub, map_mul, PsiHom_smul, map_one, hΨC, hφ1x, hφ2x, hy]
    rw [Matrix.mul_smul]
    congr 1
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, hc4, hC5]
    module
  · have hD : (C.map φ)ᵀ = C * C * C := by
      calc (C.map φ)ᵀ = (C.map φ)ᵀ * (C * C * C * C) := by
            rw [show C * C * C * C = C * C * (C * C) by noncomm_ring, hc4, Matrix.mul_one]
        _ = ((C.map φ)ᵀ * C) * (C * C * C) := by noncomm_ring
        _ = C * C * C := by rw [hCu, Matrix.one_mul]
    have hΦ : ∀ M : Matrix (Fin 3) (Fin 3) F, M.map φ = (φ : F →+* F).mapMatrix M := fun M => rfl
    have hΦs : ∀ (a : F) (M : Matrix (Fin 3) (Fin 3) F),
        (φ : F →+* F).mapMatrix (a • M) = φ a • (φ : F →+* F).mapMatrix M := fun a M =>
      Matrix.map_smul' _ _ _ φ.map_mul
    have hΦC : (φ : F →+* F).mapMatrix C = C.map φ := rfl
    have hP : (Q.map φ)ᵀ = (-x - 1) • (1 : Matrix (Fin 3) (Fin 3) F) + y • C + (x - 1) • (C * C) -
        y • (C * C * C) := by
      rw [hΦ, hQ]
      simp only [map_add, map_sub, map_mul, map_one, hΦs, hΦC, Matrix.transpose_add,
        Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_one, hD,
        hφ1x, hφ2x, hy, hC6, hC5b]
      module
    have hQP := poly_unit C hc4 x y hxy
    rw [Matrix.map_smul' _ _ _ (φ.map_mul), hφ2, Matrix.transpose_smul, hP, Matrix.smul_mul,
      Matrix.mul_smul, hQP, smul_smul, smul_smul]
    have h4 : (2 : F)⁻¹ * (2 : F)⁻¹ * 4 = 1 := by field_simp; norm_num
    rw [h4, one_smul]


end S3OuterUniAlg

end CFSG.GH74.Generic.BProg.B3
