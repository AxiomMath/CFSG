module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointKernelSimilarity

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel

open Matrix CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalPointAction

universe u

variable {K : Type u} [Field K] {d : ℕ}

theorem derivedPointAction_inclusion (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    derivedPointAction Q A = similarityPointAction Q (matrixDerivedInclusion Q A) := rfl

theorem derivedPointAction_eq_one_iff (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0)
    (A : matrixDerived Q) :
    derivedPointAction Q A = 1 ↔ A ∈ matrixDerivedScalars Q := by
  rw [derivedPointAction_inclusion, similarityPointAction_eq_one_iff Q hQ hS,
    mem_matrixDerivedScalars_iff]
  change ((1 : K ≃+* K) = 1 ∧
    ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = A.val) ↔
      ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = A.val
  exact and_iff_right rfl

theorem derivedPointAction_kernel (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    (derivedPointAction Q).ker = matrixDerivedScalars Q := by
  ext A
  exact derivedPointAction_eq_one_iff Q hQ hS A

theorem projectivePointAction_kernel (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    (CatalogueBOrthogonalPointData.projectivePointAction Q).ker = ⊥ := by
  change (QuotientGroup.lift (matrixDerivedScalars Q) (derivedPointAction Q)
    (derivedScalars_le_pointKernel Q)).ker = ⊥
  rw [QuotientGroup.ker_lift, derivedPointAction_kernel Q hQ hS]
  exact (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge

theorem projectivePointAction_injective (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    Function.Injective (CatalogueBOrthogonalPointData.projectivePointAction Q) :=
  (MonoidHom.ker_eq_bot_iff _).mp (projectivePointAction_kernel Q hQ hS)

theorem projectivePointAction_representative (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) :
    CatalogueBOrthogonalPointData.projectivePointAction Q (matrixProjectiveProjection Q A) =
      similarityPointAction Q (matrixDerivedInclusion Q A) :=
  projectivePointAction_mk Q A

theorem projectivePointAction_representative_submodule (Q : QuadraticForm K (Fin d → K))
    (A : matrixDerived Q) (L : Points Q) :
    (CatalogueBOrthogonalPointData.projectivePointAction Q
      (matrixProjectiveProjection Q A) L).val =
        L.val.map (matrixLinearEquiv A.val).toLinearMap :=
  projectivePointAction_mk_submodule Q A L

theorem orthogonal_original_point_kernel (Q : QuadraticForm K (Fin d → K))
    (hQ : Q.polarBilin.Nondegenerate)
    (hS : ∃ S : Submodule K (Fin d → K),
      Module.finrank K S = 3 ∧ ∀ v ∈ S, Q v = 0) :
    (∀ g : similarityPairs Q, similarityPointAction Q g = 1 ↔ g.val.right = 1 ∧
      ∃ a : Kˣ, GeneralLinearGroup.scalar (Fin d) a = g.val.left) ∧
    (derivedPointAction Q).ker = matrixDerivedScalars Q ∧
    Function.Injective (CatalogueBOrthogonalPointData.projectivePointAction Q) :=
  ⟨similarityPointAction_eq_one_iff Q hQ hS,
    derivedPointAction_kernel Q hQ hS, projectivePointAction_injective Q hQ hS⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalPointKernel
