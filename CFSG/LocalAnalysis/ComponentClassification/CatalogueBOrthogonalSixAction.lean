module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixActionSimilitudes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixPfaffianCovariance
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem six_base_smul (delta a : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    (algebraMap K (extension delta) a) • X = a • X := by
  apply Matrix.ext
  intro i j
  exact (Algebra.smul_def a (X i j)).symm

theorem six_hermitian_inverse_right (delta : K) (g : sixSimilitudes delta) :
    (sixBar delta g.val.val).transpose * sixGram (extension delta) =
      (sixMultiplier delta g : K) • (sixGram (extension delta) * g.val⁻¹.val) := by
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) (extension delta) => M * g.val⁻¹.val)
    (sixMultiplier_spec delta g)
  simpa only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Matrix.smul_mul] using h

theorem six_hermitian_inverse_left (delta : K) (g : sixSimilitudes delta) :
    sixGram (extension delta) * sixBar delta g.val.val =
      (sixMultiplier delta g : K) • (g.val⁻¹.val.transpose * sixGram (extension delta)) := by
  have h := congrArg Matrix.transpose (six_hermitian_inverse_right delta g)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, sixGram_transpose,
    Matrix.transpose_smul] using h

@[expose] def sixCongruenceMatrix (delta : K) (g : sixSimilitudes delta)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    Matrix (Fin 4) (Fin 4) (extension delta) :=
  ((sixMultiplier delta g : K)⁻¹) • (g.val.val * X * g.val.val.transpose)

theorem sixCongruenceMatrix_mem (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSimilitudes delta) (X : sixSubmodule delta) :
    sixCongruenceMatrix delta g X.val ∈ sixSubmodule delta := by
  constructor
  · rw [sixCongruenceMatrix, Matrix.transpose_smul,
      congruence_skew g.val.val X.val X.property.1, smul_neg]
  · rw [sixCongruenceMatrix, sharp_base_smul,
      sharp_congruence (X := X.val) (extension_two_ne_zero delta h2) g.val X.property.1,
      sixMultiplier_det, six_base_smul, X.property.2]
    have hmu : (sixMultiplier delta g : K) ≠ 0 := Units.ne_zero _
    calc
      (sixMultiplier delta g : K)⁻¹ • ((sixMultiplier delta g : K) ^ 2 •
          (g.val⁻¹.val.transpose *
            (sixGram (extension delta) * sixBar delta X.val * sixGram (extension delta)) *
            g.val⁻¹.val)) =
          (sixMultiplier delta g : K) •
            (g.val⁻¹.val.transpose *
              (sixGram (extension delta) * sixBar delta X.val * sixGram (extension delta)) *
              g.val⁻¹.val) := by
        rw [smul_smul]
        congr 1
        field_simp
      _ = sixGram (extension delta) * sixBar delta
          ((sixMultiplier delta g : K)⁻¹ • (g.val.val * X.val * g.val.val.transpose)) *
          sixGram (extension delta) := by
        rw [sixBar_smul, sixBar_mul, sixBar_mul, sixBar_transpose]
        calc
          _ = (sixMultiplier delta g : K)⁻¹ •
              ((sixGram (extension delta) * sixBar delta g.val.val) * sixBar delta X.val *
                ((sixBar delta g.val.val).transpose * sixGram (extension delta))) := by
            rw [six_hermitian_inverse_left, six_hermitian_inverse_right,
              Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
            simp only [Matrix.mul_assoc, smul_smul]
            congr 1
            field_simp
          _ = _ := by rw [Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]

theorem sixCongruenceMatrix_one (delta : K)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixCongruenceMatrix delta 1 X = X := by
  simp [sixCongruenceMatrix]

theorem sixCongruenceMatrix_mul (delta : K) (g h : sixSimilitudes delta)
    (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    sixCongruenceMatrix delta (g * h) X =
      sixCongruenceMatrix delta g (sixCongruenceMatrix delta h X) := by
  change (sixMultiplier delta (g * h) : K)⁻¹ •
      ((g.val.val * h.val.val) * X * (g.val.val * h.val.val).transpose) = _
  simp only [sixCongruenceMatrix, map_mul, Units.val_mul, _root_.mul_inv_rev,
    Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  congr 1
  exact mul_comm _ _

@[expose] def sixCongruence (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) : sixSubmodule delta ≃ₗ[K] sixSubmodule delta where
  toFun X := ⟨sixCongruenceMatrix delta g X.val, sixCongruenceMatrix_mem delta h2 g X⟩
  invFun X := ⟨sixCongruenceMatrix delta g⁻¹ X.val, sixCongruenceMatrix_mem delta h2 g⁻¹ X⟩
  left_inv X := by
    apply Subtype.ext
    change sixCongruenceMatrix delta g⁻¹ (sixCongruenceMatrix delta g X.val) = X.val
    rw [← sixCongruenceMatrix_mul, inv_mul_cancel, sixCongruenceMatrix_one]
  right_inv X := by
    apply Subtype.ext
    change sixCongruenceMatrix delta g (sixCongruenceMatrix delta g⁻¹ X.val) = X.val
    rw [← sixCongruenceMatrix_mul, mul_inv_cancel, sixCongruenceMatrix_one]
  map_add' X Y := by
    apply Subtype.ext
    simp only [sixCongruenceMatrix, Submodule.coe_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  map_smul' a X := by
    apply Subtype.ext
    simp only [sixCongruenceMatrix, Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul]
    congr 1
    exact mul_comm _ _

theorem sixCongruence_val (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) (X : sixSubmodule delta) :
    (sixCongruence delta h2 g X).val =
      (sixMultiplier delta g : K)⁻¹ • (g.val.val * X.val * g.val.val.transpose) := rfl

theorem sixCongruence_form (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) (X : sixSubmodule delta) :
    sixForm delta (sixCongruence delta h2 g X) = sixForm delta X := by
  apply QuadraticAlgebra.algebraMap_injective (a := delta) (b := 0)
  rw [sixForm_pfaffian delta h2, sixForm_pfaffian delta h2, sixCongruence_val,
    ← six_base_smul, pfaffian_smul,
    pfaffian_congruence (X := X.val) (extension_two_ne_zero delta h2) g.val.val X.property.1,
    sixMultiplier_det]
  have hmu : (sixMultiplier delta g : K) ≠ 0 := Units.ne_zero _
  rw [← map_pow, ← mul_assoc, ← map_mul]
  have h : (sixMultiplier delta g : K)⁻¹ ^ 2 * (sixMultiplier delta g : K) ^ 2 = 1 := by
    field_simp
  rw [h, map_one, one_mul]

abbrev SixIsometries (delta : K) := TauCeti.QuadraticMap.orthogonalGroup (sixForm delta)

@[expose] def kappa (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    sixSimilitudes delta →* SixIsometries delta where
  toFun g := ⟨sixCongruence delta h2 g,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (sixCongruence_form delta h2 g)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    exact Subtype.ext (sixCongruenceMatrix_one delta X.val)
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    exact Subtype.ext (sixCongruenceMatrix_mul delta g h X.val)

theorem kappa_val (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) (X : sixSubmodule delta) :
    ((kappa delta h2 g).val X).val =
      (sixMultiplier delta g : K)⁻¹ • (g.val.val * X.val * g.val.val.transpose) := rfl

@[expose] def sixSpecialKappa (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0) :
    sixSpecialUnitary delta →* SixIsometries delta :=
  (kappa delta h2).comp (sixSpecialInclusion delta)

theorem sixSpecialKappa_val (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSpecialUnitary delta) (X : sixSubmodule delta) :
    ((sixSpecialKappa delta h2 g).val X).val = g.val.val * X.val * g.val.val.transpose := by
  rw [sixSpecialKappa, MonoidHom.comp_apply, kappa_val]
  have h := (sixMultiplier_kernel_iff delta (sixSpecialInclusion delta g)).mpr g.property
  rw [(sixMultiplier delta).mem_ker.mp h]
  simp only [Units.val_one, inv_one, one_smul]
  rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
