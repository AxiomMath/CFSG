module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFive

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K]

@[expose] def selfAdjointAnisotropicGL (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) (hX : selfAdjointForm K X ≠ 0) : GL (Fin 4) K where
  val := X.val
  inv := (selfAdjointForm K X)⁻¹ • X.val
  val_inv := by
    rw [Matrix.mul_smul, selfAdjoint_square h2, smul_smul, inv_mul_cancel₀ hX, one_smul]
  inv_val := by
    rw [Matrix.smul_mul, selfAdjoint_square h2, smul_smul, inv_mul_cancel₀ hX, one_smul]

@[expose] def selfAdjointAnisotropicSimilitude (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) (hX : selfAdjointForm K X ≠ 0) : symplecticSimilitudes K :=
  ⟨selfAdjointAnisotropicGL h2 X hX, Units.mk0 (selfAdjointForm K X) hX, by
    change X.valᵀ * symplecticGram K * X.val = selfAdjointForm K X • symplecticGram K
    rw [X.property.1, Matrix.mul_assoc, selfAdjoint_square h2, Matrix.mul_smul, Matrix.mul_one]⟩

theorem selfAdjointAnisotropicSimilitude_val (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) (hX : selfAdjointForm K X ≠ 0) :
    (selfAdjointAnisotropicSimilitude h2 X hX).val.val = X.val ∧
      (selfAdjointAnisotropicSimilitude h2 X hX).val⁻¹.val =
        (selfAdjointForm K X)⁻¹ • X.val := ⟨rfl, rfl⟩

theorem selfAdjoint_triple (h2 : (2 : K) ≠ 0) (X Y : selfAdjointSubmodule K) :
    X.val * Y.val * X.val =
      (selfAdjointForm K).polarBilin X Y • X.val - selfAdjointForm K X • Y.val := by
  have h := congrArg (fun Z : Matrix (Fin 4) (Fin 4) K => Z * X.val)
    (selfAdjoint_anticommutator h2 X Y)
  rw [Matrix.add_mul, Matrix.mul_assoc Y.val, selfAdjoint_square h2,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul] at h
  exact eq_sub_of_add_eq h

theorem selfAdjointAnisotropic_conjugation_val (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) (hX : selfAdjointForm K X ≠ 0)
    (Y : selfAdjointSubmodule K) :
    (selfAdjointConjugation (selfAdjointAnisotropicSimilitude h2 X hX) Y).val =
      ((selfAdjointForm K).polarBilin X Y / selfAdjointForm K X) • X.val - Y.val := by
  rw [selfAdjointConjugation_val,
    (selfAdjointAnisotropicSimilitude_val h2 X hX).1,
    (selfAdjointAnisotropicSimilitude_val h2 X hX).2,
    Matrix.mul_smul, selfAdjoint_triple h2, smul_sub, smul_smul, smul_smul,
    inv_mul_cancel₀ hX, one_smul]
  rw [div_eq_mul_inv, mul_comm]

theorem selfAdjoint_reflection_eq_neg_conjugation (h2 : (2 : K) ≠ 0)
    (X : selfAdjointSubmodule K) [Invertible (selfAdjointForm K X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (selfAdjointForm K) X =
      QuadraticMap.negOrthogonal (selfAdjointForm K) *
        selfAdjointOrthogonalAction h2
          (selfAdjointAnisotropicSimilitude h2 X (isUnit_of_invertible _).ne_zero) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro Y
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_reflectionOrthogonal, Subgroup.coe_mul,
    QuadraticMap.coe_negOrthogonal]
  change (TauCeti.QuadraticMap.reflection (selfAdjointForm K) X Y).val =
    -(selfAdjointConjugation
      (selfAdjointAnisotropicSimilitude h2 X (isUnit_of_invertible _).ne_zero) Y).val
  rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div,
    selfAdjointAnisotropic_conjugation_val]
  change Y.val - ((selfAdjointForm K).polarBilin X Y / selfAdjointForm K X) • X.val =
    -(((selfAdjointForm K).polarBilin X Y / selfAdjointForm K X) • X.val - Y.val)
  abel

end CFSG.ComponentClassification.CatalogueBOrthogonalFive
