module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalRealization

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenOrthogonalFourGroup

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank

section Matrix

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

theorem mem_matrixDerived_of_mem_elementaryGroup
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {M : GL (Fin d) K} (hM : matrixLinearIso M ∈ elementaryGroup Q) :
    M ∈ matrixDerived Q := by
  have h : matrixDerived Q = (⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆).comap matrixLinearIso.toMonoidHom := by
    rw [matrixDerived, matrixIsometries, Subgroup.comap_equiv_eq_map_symm',
      Subgroup.comap_equiv_eq_map_symm']
    exact (Subgroup.map_commutator _ _ _).symm
  rw [h, hE]
  exact hM

variable (v : Fin d → K)

variable {Q v}

end Matrix

end CFSG.LocalAnalysis.ComponentInitial.EvenOrthogonalFourGroup

