module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRSymmetry

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Reduction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem nonFieldCoresRigid_plus_of_higherRankCoresRigid (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hhigh : HigherRankCoresRigid n K
      (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)) :
    NonFieldCoresRigid (plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn) :=
  nonFieldCoresRigid_plus_of_cases hK hn (symmetryCoresRigid_plus hK hn) hhigh

end Reduction

end CFSG.SeitzReduction.OmegaPilot
