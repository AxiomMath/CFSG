module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public noncomputable section

open CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.IVK
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Lemma41dL3

def projEquiv (F : Type) [Field F] :
    projectiveSL 3 F ≃* StatedProj (StatedSL 3 F) :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F)).trans
    (projectiveSpecialLinearGroupEquivStatedProj 3 F)

end Lemma41dL3

end CFSG.GH74.GLS.IVK.Proofs2
