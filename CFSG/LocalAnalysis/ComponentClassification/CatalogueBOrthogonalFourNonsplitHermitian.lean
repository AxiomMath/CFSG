module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitExtension

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

@[expose] def hermitianSubmodule (delta : K) :
    Submodule K (Matrix (Fin 2) (Fin 2) (extension delta)) where
  carrier := {X | X.IsHermitian}
  zero_mem' := Matrix.isHermitian_zero
  add_mem' := fun hX hY => hX.add hY
  smul_mem' a X hX := by
    apply Matrix.IsHermitian.ext
    intro i j
    change star (a • X j i) = a • X i j
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_star, QuadraticAlgebra.im_smul,
        QuadraticAlgebra.re_smul, zero_mul, add_zero, smul_eq_mul]
      have h := congrArg QuadraticAlgebra.re (hX.apply i j)
      simpa using congrArg (a * ·) h
    · simp only [QuadraticAlgebra.im_star, QuadraticAlgebra.im_smul, smul_eq_mul]
      have h := congrArg QuadraticAlgebra.im (hX.apply i j)
      simpa only [QuadraticAlgebra.im_star, mul_neg] using congrArg (a * ·) h

theorem mem_hermitianSubmodule (delta : K) (X : Matrix (Fin 2) (Fin 2) (extension delta)) :
    X ∈ hermitianSubmodule delta ↔ X.conjTranspose = X := Iff.rfl

theorem hermitian_diagonal (delta : K) (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) (i : Fin 2) :
    X.val i i = algebraMap K (extension delta) (X.val i i).re :=
  (conjugation_fixed_iff delta h2 _).mp (X.property.apply i i)

theorem hermitian_lower (delta : K) (X : hermitianSubmodule delta) :
    X.val 1 0 = star (X.val 0 1) := (X.property.apply 1 0).symm

@[expose] def hermitianCoordinates (delta : K) (h2 : (2 : K) ≠ 0) :
    (Fin 4 → K) ≃ₗ[K] hermitianSubmodule delta where
  toFun x := ⟨!![algebraMap K (extension delta) (x 0), ⟨x 2, x 3⟩;
      star (⟨x 2, x 3⟩ : extension delta), algebraMap K (extension delta) (x 1)], by
    apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact (conjugation delta).commutes (x 0)
    · exact star_star _
    · rfl
    · exact (conjugation delta).commutes (x 1)⟩
  invFun X := ![(X.val 0 0).re, (X.val 1 1).re, (X.val 0 1).re, (X.val 0 1).im]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv X := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact (hermitian_diagonal delta h2 X 0).symm
    · exact QuadraticAlgebra.mk_eta _
    · change star (⟨(X.val 0 1).re, (X.val 0 1).im⟩ : extension delta) = X.val 1 0
      rw [QuadraticAlgebra.mk_eta, hermitian_lower]
    · exact (hermitian_diagonal delta h2 X 1).symm
  map_add' x y := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · exact map_add (algebraMap K (extension delta)) _ _
    · rfl
    · change star (⟨x 2 + y 2, x 3 + y 3⟩ : extension delta) =
        star (⟨x 2, x 3⟩ : extension delta) + star (⟨y 2, y 3⟩ : extension delta)
      exact star_add (⟨x 2, x 3⟩ : extension delta) (⟨y 2, y 3⟩ : extension delta)
    · exact map_add (algebraMap K (extension delta)) _ _
  map_smul' a x := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    · change algebraMap K (extension delta) (a * x 0) =
        a • algebraMap K (extension delta) (x 0)
      apply QuadraticAlgebra.ext <;> simp
    · rfl
    · change star (⟨a * x 2, a * x 3⟩ : extension delta) =
        a • star (⟨x 2, x 3⟩ : extension delta)
      apply QuadraticAlgebra.ext <;> simp [mul_neg]
    · change algebraMap K (extension delta) (a * x 1) =
        a • algebraMap K (extension delta) (x 1)
      apply QuadraticAlgebra.ext <;> simp

theorem hermitianCoordinates_val (delta : K) (h2 : (2 : K) ≠ 0) (x : Fin 4 → K) :
    (hermitianCoordinates delta h2 x).val =
      !![algebraMap K (extension delta) (x 0), ⟨x 2, x 3⟩;
        star (⟨x 2, x 3⟩ : extension delta), algebraMap K (extension delta) (x 1)] := rfl

theorem hermitianCoordinates_symm_apply (delta : K) (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) :
    (hermitianCoordinates delta h2).symm X =
      ![(X.val 0 0).re, (X.val 1 1).re, (X.val 0 1).re, (X.val 0 1).im] := rfl

theorem hermitian_finrank (delta : K) (h2 : (2 : K) ≠ 0) :
    Module.finrank K (hermitianSubmodule delta) = 4 := by
  rw [← (hermitianCoordinates delta h2).finrank_eq]
  simp

@[expose] def hermitianForm (delta : K) : QuadraticForm K (hermitianSubmodule delta) :=
  let entry (i j : Fin 2) := ((QuadraticAlgebra.reₗ (a := delta) (b := 0)).comp
    (Matrix.entryLinearMap K (extension delta) i j)).comp (hermitianSubmodule delta).subtype
  let imag := ((QuadraticAlgebra.imₗ (a := delta) (b := 0)).comp
    (Matrix.entryLinearMap K (extension delta) (0 : Fin 2) 1)).comp
      (hermitianSubmodule delta).subtype
  linMulLin (entry 0 0) (entry 1 1) - linMulLin (entry 0 1) (entry 0 1) +
    delta • linMulLin imag imag

theorem hermitianForm_apply (delta : K) (X : hermitianSubmodule delta) :
    hermitianForm delta X = (X.val 0 0).re * (X.val 1 1).re -
      (X.val 0 1).re ^ 2 + delta * (X.val 0 1).im ^ 2 := by
  change (X.val 0 0).re * (X.val 1 1).re -
    (X.val 0 1).re * (X.val 0 1).re +
      delta * ((X.val 0 1).im * (X.val 0 1).im) = _
  simp only [pow_two]

theorem hermitianForm_det (delta : K) (h2 : (2 : K) ≠ 0)
    (X : hermitianSubmodule delta) :
    algebraMap K (extension delta) (hermitianForm delta X) = X.val.det := by
  rw [Matrix.det_fin_two, hermitian_diagonal delta h2 X 0,
    hermitian_diagonal delta h2 X 1, hermitian_lower,
    ← QuadraticAlgebra.algebraMap_norm_eq_mul_star, ← map_mul, ← map_sub,
    extension_norm, hermitianForm_apply]
  congr 1
  ring

theorem hermitianForm_polar (delta : K) (X Y : hermitianSubmodule delta) :
    (hermitianForm delta).polarBilin X Y =
      (X.val 0 0).re * (Y.val 1 1).re + (X.val 1 1).re * (Y.val 0 0).re -
      2 * (X.val 0 1).re * (Y.val 0 1).re +
        2 * delta * (X.val 0 1).im * (Y.val 0 1).im := by
  rw [polarBilin_apply_apply, polar, hermitianForm_apply, hermitianForm_apply,
    hermitianForm_apply]
  change ((X.val 0 0).re + (Y.val 0 0).re) * ((X.val 1 1).re + (Y.val 1 1).re) -
      ((X.val 0 1).re + (Y.val 0 1).re) ^ 2 +
      delta * ((X.val 0 1).im + (Y.val 0 1).im) ^ 2 -
      ((X.val 0 0).re * (X.val 1 1).re - (X.val 0 1).re ^ 2 +
        delta * (X.val 0 1).im ^ 2) -
      ((Y.val 0 0).re * (Y.val 1 1).re - (Y.val 0 1).re ^ 2 +
        delta * (Y.val 0 1).im ^ 2) = _
  ring

theorem hermitianForm_nondegenerate (delta : K) (hns : ¬ IsSquare delta)
    (h2 : (2 : K) ≠ 0) : (hermitianForm delta).polarBilin.Nondegenerate := by
  have hd : delta ≠ 0 := by rintro rfl; exact hns IsSquare.zero
  have left : (hermitianForm delta).polarBilin.SeparatingLeft := by
    intro X hX
    have h0 := hX (hermitianCoordinates delta h2 ![0, 1, 0, 0])
    have h1 := hX (hermitianCoordinates delta h2 ![1, 0, 0, 0])
    have h2' := hX (hermitianCoordinates delta h2 ![0, 0, 1, 0])
    have h3 := hX (hermitianCoordinates delta h2 ![0, 0, 0, 1])
    rw [hermitianForm_polar] at h0 h1 h2' h3
    have hz0 : (X.val 0 0).re = 0 := by
      simpa [hermitianCoordinates, QuadraticAlgebra.re_one] using h0
    have hz1 : (X.val 1 1).re = 0 := by
      simpa [hermitianCoordinates, QuadraticAlgebra.re_one] using h1
    have hz2 : (X.val 0 1).re = 0 := by
      have hmul : (2 : K) * (X.val 0 1).re = 0 := by
        simpa [hermitianCoordinates] using congrArg Neg.neg h2'
      exact (mul_eq_zero.mp hmul).resolve_left h2
    have hz3 : (X.val 0 1).im = 0 := by
      have hmul : (2 * delta) * (X.val 0 1).im = 0 := by
        simpa [hermitianCoordinates] using h3
      exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero h2 hd)
    apply (hermitianCoordinates delta h2).symm.injective
    funext i
    fin_cases i <;> simpa [hermitianCoordinates] using (by assumption)
  refine ⟨left, ?_⟩
  intro X hX
  apply left X
  intro Y
  have h := hX Y
  rw [hermitianForm_polar] at h ⊢
  linear_combination h

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
