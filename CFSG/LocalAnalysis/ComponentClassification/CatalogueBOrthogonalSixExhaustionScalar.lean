module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem six_generator_ne_zero (delta : K) : (QuadraticAlgebra.omega : extension delta) ≠ 0 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  simp at hi

theorem six_scalar_generator_hermitian (delta : K) :
    (sixBar delta ((QuadraticAlgebra.omega : extension delta) •
      (1 : Matrix (Fin 4) (Fin 4) (extension delta)))).transpose *
        sixGram (extension delta) *
          ((QuadraticAlgebra.omega : extension delta) •
            (1 : Matrix (Fin 4) (Fin 4) (extension delta))) =
      (-delta) • sixGram (extension delta) := by
  have hb : sixBar delta ((QuadraticAlgebra.omega : extension delta) •
      (1 : Matrix (Fin 4) (Fin 4) (extension delta))) =
      -(QuadraticAlgebra.omega : extension delta) •
        (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      apply QuadraticAlgebra.ext <;> simp [sixBar, conjugation]
    · simp [sixBar, hij]
  rw [hb, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [mul_neg]
  have ht : (QuadraticAlgebra.omega : extension delta) * QuadraticAlgebra.omega =
      algebraMap K (extension delta) delta := by
    simpa only [pow_two] using generator_square delta
  rw [ht, ← map_neg, six_base_smul]

theorem six_scalar_generator_det (delta : K) :
    ((QuadraticAlgebra.omega : extension delta) •
      (1 : Matrix (Fin 4) (Fin 4) (extension delta))).det =
      algebraMap K (extension delta) ((-delta) ^ 2) := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  change (QuadraticAlgebra.omega : extension delta) ^ 4 =
    algebraMap K (extension delta) ((-delta) ^ 2)
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, generator_square]
  rw [← map_pow]
  congr 1
  ring

@[expose] def sixGeneratorD (delta : K) [Fact (¬ IsSquare delta)] : sixSimilitudes delta :=
  let hd : delta ≠ 0 := by
    intro h
    exact (Fact.out : ¬ IsSquare delta) (h ▸ IsSquare.zero)
  let g : GL (Fin 4) (extension delta) :=
    { val := (QuadraticAlgebra.omega : extension delta) • 1
      inv := (QuadraticAlgebra.omega : extension delta)⁻¹ • 1
      val_inv := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          mul_inv_cancel₀ (six_generator_ne_zero delta), one_smul]
      inv_val := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
          inv_mul_cancel₀ (six_generator_ne_zero delta), one_smul] }
  ⟨g, Units.mk0 (-delta) (neg_ne_zero.mpr hd),
    six_scalar_generator_hermitian delta, six_scalar_generator_det delta⟩

theorem sixGeneratorD_val (delta : K) [Fact (¬ IsSquare delta)] :
    (sixGeneratorD delta).val.val = (QuadraticAlgebra.omega : extension delta) •
      (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := rfl

theorem sixGeneratorD_multiplier (delta : K) [Fact (¬ IsSquare delta)] :
    (sixMultiplier delta (sixGeneratorD delta) : K) = -delta := by
  have hmul := sixMultiplier_spec delta (sixGeneratorD delta)
  rw [sixGeneratorD_val, six_scalar_generator_hermitian] at hmul
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) (extension delta) => (M 0 2).re) hmul
  simpa [sixGram, smul_eq_mul, QuadraticAlgebra.re_one] using he.symm

theorem sixGeneratorD_action (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    kappa delta h2 (sixGeneratorD delta) = QuadraticMap.negOrthogonal (sixForm delta) := by
  have hd : delta ≠ 0 := by
    intro h
    exact (Fact.out : ¬ IsSquare delta) (h ▸ IsSquare.zero)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  rw [kappa_val, sixGeneratorD_multiplier, sixGeneratorD_val,
    QuadraticMap.coe_negOrthogonal]
  change (-delta)⁻¹ • (((QuadraticAlgebra.omega : extension delta) •
    (1 : Matrix (Fin 4) (Fin 4) (extension delta))) * X.val *
    ((QuadraticAlgebra.omega : extension delta) •
      (1 : Matrix (Fin 4) (Fin 4) (extension delta))).transpose) = -X.val
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]
  have ht : (QuadraticAlgebra.omega : extension delta) * QuadraticAlgebra.omega =
      algebraMap K (extension delta) delta := by
    simpa only [pow_two] using generator_square delta
  rw [ht, six_base_smul, smul_smul]
  have hm : (-delta)⁻¹ * delta = -1 := by
    rw [inv_neg, neg_mul, inv_mul_cancel₀ hd]
  rw [hm, neg_one_smul]

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
