module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourNonsplitReflection
public import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

open Matrix QuadraticMap

universe u

variable {K : Type u} [Field K] (delta : K)

@[expose] def conjugateGL : GL (Fin 2) (extension delta) →* GL (Fin 2) (extension delta) :=
  GeneralLinearGroup.map (conjugation delta).toRingHom

theorem conjugateGL_val (A : GL (Fin 2) (extension delta)) :
    (conjugateGL delta A).val = A.val.map (conjugation delta) := rfl

theorem conjugateGL_conjTranspose (A : GL (Fin 2) (extension delta)) :
    (conjugateGL delta A).val.conjTranspose = A.val.transpose := by
  apply Matrix.ext
  intro i j
  exact star_star _

theorem conjugateGL_normDeterminant (A : GL (Fin 2) (extension delta)) :
    normDeterminant delta (conjugateGL delta A) = normDeterminant delta A := by
  apply Units.ext
  change QuadraticAlgebra.norm (A.val.map (conjugation delta)).det =
    QuadraticAlgebra.norm A.val.det
  change QuadraticAlgebra.norm ((conjugation delta).toRingHom.mapMatrix A.val).det = _
  rw [← RingHom.map_det (conjugation delta).toRingHom]
  exact QuadraticAlgebra.norm_star _

@[expose] def conjugateD : normDeterminantOne delta →* normDeterminantOne delta where
  toFun A := ⟨conjugateGL delta A.val, by
    change normDeterminant delta (conjugateGL delta A.val) = 1
    rw [conjugateGL_normDeterminant]
    exact A.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

theorem gamma_rho (h2 : (2 : K) ≠ 0) (A : normDeterminantOne delta) :
    gamma delta h2 * rho delta h2 A =
      rho delta h2 (conjugateD delta A) * gamma delta h2 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change (A.val.val * X.val * A.val.val.conjTranspose).transpose =
    (conjugateGL delta A.val).val * X.val.transpose *
      (conjugateGL delta A.val).val.conjTranspose
  rw [conjugateGL_conjTranspose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]
  rfl

theorem gamma_inv (h2 : (2 : K) ≠ 0) : (gamma delta h2)⁻¹ = gamma delta h2 :=
  inv_eq_of_mul_eq_one_right (gamma_mul_gamma delta h2)

@[expose] def fullHermitianImage (h2 : (2 : K) ≠ 0) : Subgroup (HermitianIsometries delta) where
  carrier := {g | ∃ A : normDeterminantOne delta,
    g = rho delta h2 A ∨ g = rho delta h2 A * gamma delta h2}
  one_mem' := ⟨1, Or.inl (map_one _).symm⟩
  mul_mem' {g} {h} hg hh := by
    obtain ⟨A, rfl | rfl⟩ := hg <;> obtain ⟨B, rfl | rfl⟩ := hh
    · exact ⟨A * B, Or.inl (map_mul _ _ _).symm⟩
    · refine ⟨A * B, Or.inr ?_⟩
      rw [map_mul, mul_assoc]
    · refine ⟨A * conjugateD delta B, Or.inr ?_⟩
      rw [map_mul, mul_assoc, gamma_rho, ← mul_assoc]
    · refine ⟨A * conjugateD delta B, Or.inl ?_⟩
      rw [map_mul, mul_assoc, ← mul_assoc (gamma delta h2), gamma_rho,
        mul_assoc, gamma_mul_gamma, mul_one]
  inv_mem' {g} hg := by
    obtain ⟨A, rfl | rfl⟩ := hg
    · exact ⟨A⁻¹, Or.inl (map_inv _ _).symm⟩
    · refine ⟨conjugateD delta A⁻¹, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, gamma_inv, ← map_inv, gamma_rho]

theorem reflection_mem_fullHermitianImage [Finite K] [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (X : hermitianSubmodule delta)
    [Invertible (hermitianForm delta X)] :
    TauCeti.QuadraticMap.reflectionOrthogonal (hermitianForm delta) X ∈
      fullHermitianImage delta h2 := by
  obtain ⟨A, hA⟩ := hermitian_reflection_eq_rho_gamma delta h2 X
  exact ⟨A, Or.inr hA⟩

theorem fullHermitianImage_eq_top [Finite K] [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : fullHermitianImage delta h2 = ⊤ := by
  let : NeZero (2 : K) := ⟨h2⟩
  let : Invertible (2 : K) := invertibleOfNonzero h2
  let : FiniteDimensional K (hermitianSubmodule delta) :=
    Module.Finite.equiv (hermitianCoordinates delta h2)
  apply TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem (hermitianForm delta)
    (QuadraticMap.nondegenerate_polar_iff.mp
      (hermitianForm_nondegenerate delta (Fact.out (p := ¬ IsSquare delta)) h2))
  intro X _
  exact reflection_mem_fullHermitianImage delta h2 X

theorem hermitian_isometry_exhaustion [Finite K] [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : HermitianIsometries delta) :
    ∃ A : normDeterminantOne delta, g = rho delta h2 A ∨
      g = rho delta h2 A * gamma delta h2 := by
  have hg : g ∈ fullHermitianImage delta h2 := by
    rw [fullHermitianImage_eq_top delta h2]
    trivial
  exact hg

end CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit
