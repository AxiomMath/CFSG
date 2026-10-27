module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem six_XH_barXH (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    (X.val * sixGram (extension delta)) *
        (sixBar delta X.val * sixGram (extension delta)) =
      -(sixForm delta X) • (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
  calc
    _ = X.val * (sixGram (extension delta) * sixBar delta X.val *
        sixGram (extension delta)) := by simp only [Matrix.mul_assoc]
    _ = X.val * sharp X.val := by rw [← X.property.2]
    _ = _ := by
      rw [mul_sharp (extension_two_ne_zero delta h2) X.property.1,
        ← sixForm_pfaffian delta h2, ← map_neg, six_base_smul]

theorem six_barXH_XH (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    (sixBar delta X.val * sixGram (extension delta)) *
        (X.val * sixGram (extension delta)) =
      -(sixForm delta X) • (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
  have hh := congrArg
    (fun M : Matrix (Fin 4) (Fin 4) (extension delta) =>
      sixGram (extension delta) * M * sixGram (extension delta))
    (sharp_mul (extension_two_ne_zero delta h2) X.property.1)
  rw [X.property.2, ← sixForm_pfaffian delta h2, ← map_neg, six_base_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sixGram_square] at hh
  calc
    _ = sixGram (extension delta) *
        ((sixGram (extension delta) * sixBar delta X.val * sixGram (extension delta)) * X.val) *
        sixGram (extension delta) := by
      simp only [← Matrix.mul_assoc, sixGram_square, Matrix.one_mul]
    _ = _ := hh

@[expose] def sixAnisotropicGL (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0) :
    GL (Fin 4) (extension delta) where
  val := X.val * sixGram (extension delta)
  inv := -(sixForm delta X)⁻¹ • (sixBar delta X.val * sixGram (extension delta))
  val_inv := by
    rw [Matrix.mul_smul, six_XH_barXH delta h2, smul_smul]
    simp [inv_mul_cancel₀ hX]
  inv_val := by
    rw [Matrix.smul_mul, six_barXH_XH delta h2, smul_smul]
    simp [inv_mul_cancel₀ hX]

theorem sixAnisotropicGL_val (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0) :
    (sixAnisotropicGL delta h2 X hX).val = X.val * sixGram (extension delta) := rfl

theorem six_XH_hermitian (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    (sixBar delta (X.val * sixGram (extension delta))).transpose *
        sixGram (extension delta) * (X.val * sixGram (extension delta)) =
      (sixForm delta X) • sixGram (extension delta) := by
  rw [sixBar_mul, sixBar_gram, Matrix.transpose_mul, sixGram_transpose,
    ← sixBar_transpose, X.property.1, sixBar_neg]
  calc
    _ = - (sixGram (extension delta) *
        ((sixBar delta X.val * sixGram (extension delta)) *
          (X.val * sixGram (extension delta)))) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [six_barXH_XH delta h2, Matrix.mul_smul, Matrix.mul_one,
        neg_smul, neg_neg]

theorem six_XH_det (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (X : sixSubmodule delta) :
    (X.val * sixGram (extension delta)).det =
      algebraMap K (extension delta) ((sixForm delta X) ^ 2) := by
  rw [Matrix.det_mul, sixGram_det, mul_one,
    skew_det (extension_two_ne_zero delta h2) X.property.1,
    ← sixForm_pfaffian delta h2, map_pow]

@[expose] def sixAnisotropicD (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0) :
    sixSimilitudes delta :=
  ⟨sixAnisotropicGL delta h2 X hX, Units.mk0 (sixForm delta X) hX,
    six_XH_hermitian delta h2 X, six_XH_det delta h2 X⟩

theorem sixAnisotropicD_val (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0) :
    (sixAnisotropicD delta h2 X hX).val.val = X.val * sixGram (extension delta) := rfl

theorem sixAnisotropicD_multiplier (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0) :
    sixMultiplier delta (sixAnisotropicD delta h2 X hX) =
      Units.mk0 (sixForm delta X) hX := by
  apply sixMultiplier_eq_of_equation
  exact six_XH_hermitian delta h2 X

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
