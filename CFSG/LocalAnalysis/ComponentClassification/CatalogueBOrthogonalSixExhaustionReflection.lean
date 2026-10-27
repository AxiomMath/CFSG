module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixExhaustionAnisotropic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixActionGamma

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem six_polarized_product (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X Y : sixSubmodule delta) :
    X.val * sharp Y.val + Y.val * sharp X.val =
      -((sixForm delta).polarBilin X Y) •
        (1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
  rw [polarized_product (extension_two_ne_zero delta h2) X.property.1 Y.property.1]
  have hp : pfaffian (X.val + Y.val) - pfaffian X.val - pfaffian Y.val =
      algebraMap K (extension delta) ((sixForm delta).polarBilin X Y) := by
    rw [polarBilin_apply_apply, polar, map_sub, map_sub,
      sixForm_pfaffian delta h2, sixForm_pfaffian delta h2, sixForm_pfaffian delta h2]
    rfl
  rw [hp, ← map_neg, six_base_smul]

theorem six_skew_triple (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X Y : sixSubmodule delta) :
    X.val * sharp Y.val * X.val =
      -((sixForm delta).polarBilin X Y) • X.val + sixForm delta X • Y.val := by
  have hh := congrArg (fun Z : Matrix (Fin 4) (Fin 4) (extension delta) => Z * X.val)
    (six_polarized_product delta h2 X Y)
  rw [Matrix.add_mul, Matrix.mul_assoc Y.val,
    sharp_mul (extension_two_ne_zero delta h2) X.property.1,
    ← sixForm_pfaffian delta h2, ← map_neg, six_base_smul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at hh
  calc
    _ = -((sixForm delta).polarBilin X Y) • X.val - (-(sixForm delta X) • Y.val) :=
      eq_sub_of_add_eq hh
    _ = _ := by simp only [neg_smul, sub_neg_eq_add]

theorem sixAnisotropic_gamma_action (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) (hX : sixForm delta X ≠ 0)
    (Y : sixSubmodule delta) :
    (((kappa delta h2 (sixAnisotropicD delta h2 X hX) * sixGamma delta).val) Y).val =
      (((sixForm delta).polarBilin X Y) / sixForm delta X) • X.val - Y.val := by
  change ((kappa delta h2 (sixAnisotropicD delta h2 X hX)).val
    ((sixGamma delta).val Y)).val = _
  rw [kappa_val, sixAnisotropicD_multiplier, Units.val_mk0,
    sixGamma_val, sixAnisotropicD_val, Matrix.transpose_mul,
    sixGram_transpose, X.property.1]
  calc
    (sixForm delta X)⁻¹ •
        ((X.val * sixGram (extension delta)) * sixBar delta Y.val *
          (sixGram (extension delta) * -X.val)) =
        -(sixForm delta X)⁻¹ • (X.val * sharp Y.val * X.val) := by
      rw [Y.property.2]
      simp only [Matrix.mul_neg, smul_neg, neg_smul, Matrix.mul_assoc]
    _ = _ := by
      rw [six_skew_triple delta h2, smul_add, smul_smul, smul_smul]
      have hq : -(sixForm delta X)⁻¹ * sixForm delta X = -1 := by
        rw [neg_mul, inv_mul_cancel₀ hX]
      have hb : -(sixForm delta X)⁻¹ * -((sixForm delta).polarBilin X Y) =
          (sixForm delta).polarBilin X Y / sixForm delta X := by
        rw [neg_mul_neg, div_eq_mul_inv, mul_comm]
      rw [hq, hb, neg_one_smul, sub_eq_add_neg]

theorem six_reflection_eq_neg_anisotropic_gamma (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : sixSubmodule delta) [Invertible (sixForm delta X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (sixForm delta) X =
      QuadraticMap.negOrthogonal (sixForm delta) *
        (kappa delta h2 (sixAnisotropicD delta h2 X (isUnit_of_invertible _).ne_zero) *
          sixGamma delta) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Y
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, Subgroup.coe_mul,
    QuadraticMap.coe_negOrthogonal]
  change (TauCeti.QuadraticMap.reflection (sixForm delta) X Y).val =
    -((((kappa delta h2 (sixAnisotropicD delta h2 X
      (isUnit_of_invertible _).ne_zero) * sixGamma delta).val) Y).val)
  rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div, sixAnisotropic_gamma_action]
  change Y.val - ((sixForm delta).polarBilin X Y / sixForm delta X) • X.val =
    -(((sixForm delta).polarBilin X Y / sixForm delta X) • X.val - Y.val)
  abel

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
