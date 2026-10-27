module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructureNormal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix CFSG.ComponentClassification
open CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
open CFSG.ComponentClassification.CatalogueBOrthogonalSix

variable {K : Type*} [Field K] (delta : K)

@[expose] def sixScalarGL (c : Kˣ) : GL (Fin 4) (extension delta) :=
  GeneralLinearGroup.scalar (Fin 4) (Units.map (algebraMap K (extension delta)).toMonoidHom c)

theorem sixScalarGL_val (c : Kˣ) :
    (sixScalarGL delta c).val = (c : K) • (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
  rw [sixScalarGL, GeneralLinearGroup.coe_scalar, ← six_base_smul, Matrix.smul_one_eq_diagonal]
  rfl

theorem sixBar_one : sixBar delta (1 : Matrix (Fin 4) (Fin 4) (extension delta)) = 1 := by
  apply Matrix.ext
  intro i j
  rw [sixBar_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem sixScalarGL_equation (c : Kˣ) :
    (sixBar delta (sixScalarGL delta c).val).transpose * sixGram (extension delta) *
      (sixScalarGL delta c).val = (((c ^ 2 : Kˣ) : K)) • sixGram (extension delta) := by
  rw [sixScalarGL_val, sixBar_smul, sixBar_one, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    Units.val_pow_eq_pow_val, pow_two]

theorem sixScalarGL_det (c : Kˣ) :
    (sixScalarGL delta c).val.det =
      algebraMap K (extension delta) ((((c ^ 2 : Kˣ) : K)) ^ 2) := by
  have hd := congrArg Units.val (GeneralLinearGroup.det_scalar (n := Fin 4)
    (Units.map (algebraMap K (extension delta)).toMonoidHom c))
  rw [GeneralLinearGroup.val_det_apply, Fintype.card_fin, Units.val_pow_eq_pow_val,
    Units.coe_map] at hd
  rw [sixScalarGL, hd, Units.val_pow_eq_pow_val, ← pow_mul]
  simp

@[expose] def sixScalar (c : Kˣ) : sixSimilitudes delta :=
  ⟨sixScalarGL delta c, c ^ 2, sixScalarGL_equation delta c, sixScalarGL_det delta c⟩

theorem sixMultiplier_sixScalar (c : Kˣ) : sixMultiplier delta (sixScalar delta c) = c ^ 2 :=
  sixMultiplier_eq_of_equation delta _ _ (sixScalarGL_equation delta c)

variable [Fact (¬ IsSquare delta)]

theorem kappa_sixScalar (h2 : (2 : K) ≠ 0) (c : Kˣ) : kappa delta h2 (sixScalar delta c) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  rw [kappa_val, sixMultiplier_sixScalar]
  change ((c ^ 2 : Kˣ) : K)⁻¹ • ((sixScalarGL delta c).val * X.val *
    (sixScalarGL delta c).val.transpose) = X.val
  rw [sixScalarGL_val, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul,
    Units.val_pow_eq_pow_val]
  have hc : (c : K) ≠ 0 := c.ne_zero
  rw [show ((c : K) ^ 2)⁻¹ * (c : K) * (c : K) = 1 by field_simp, one_smul]

theorem kappa_mem_sixSpecialImage_of_multiplier_eq_sq (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) {c : Kˣ} (hg : sixMultiplier delta g = c ^ 2) :
    kappa delta h2 g ∈ sixSpecialImage delta h2 := by
  have h := six_kappa_mem_specialImage_of_multiplier delta h2 (g * sixScalar delta c⁻¹) (by
    rw [map_mul, hg, sixMultiplier_sixScalar, inv_pow, mul_inv_cancel])
  rwa [map_mul, kappa_sixScalar, mul_one] at h

theorem six_sq_mem_specialImage (h2 : (2 : K) ≠ 0) (z : SixIsometries delta) :
    z ^ 2 ∈ sixSpecialImage delta h2 := by
  obtain ⟨g, rfl | rfl⟩ := six_full_isometry_exhaustion delta h2 z
  · rw [← map_pow]
    exact kappa_mem_sixSpecialImage_of_multiplier_eq_sq delta h2 _
      (c := sixMultiplier delta g) (map_pow _ _ _)
  · have heq : (kappa delta h2 g * sixGamma delta) ^ 2 =
        kappa delta h2 (g * sixConjugateD delta g) := by
      rw [map_mul, ← sixGamma_kappa_gamma]
      simp only [pow_two, mul_assoc]
    rw [heq]
    apply kappa_mem_sixSpecialImage_of_multiplier_eq_sq delta h2 _ (c := sixMultiplier delta g)
    rw [map_mul, sixMultiplier_conjugate, pow_two]

variable [Finite K]

theorem sixSpecialImage_quasisimple (h2 : (2 : K) ≠ 0) :
    CFSG.IsQuasisimple (sixSpecialImage delta h2) :=
  sixSpecialKappa_range_quasisimple delta h2

theorem six_commutator_eq (h2 : (2 : K) ≠ 0) :
    commutator (SixIsometries delta) = sixSpecialImage delta h2 :=
  commutator_eq_of_isPerfect_of_forall_sq_mem (sixSpecialImage_quasisimple delta h2).1
    (six_sq_mem_specialImage delta h2)

end CFSG.LocalAnalysis.ComponentInitial
