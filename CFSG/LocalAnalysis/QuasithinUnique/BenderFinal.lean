module

public import CFSG.LocalAnalysis.QuasithinUnique.MilestoneInputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Alt
public import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassical
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalSmall
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCat
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ4Proof
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTitsProof

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.K1

theorem benderBranch_of_certificates
    (hTitsX : TitsNoStronglyClosedElemAbelian)
    (hTitsA : TitsSylowCentralizingAutInner)
    (hJ4 : SelfCentralizingFusionData (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :
    BenderBranch :=
  benderBranch_of_inputs k1_alt k1_oddClassical k1_evenClassical (k1_exceptional hTitsX hTitsA)
    k1_smallLinear (k1_sporadic hJ4)

theorem benderBranch_of_tits
    (hTitsX : TitsNoStronglyClosedElemAbelian)
    (hTitsA : TitsSylowCentralizingAutInner) : BenderBranch :=
  benderBranch_of_certificates hTitsX hTitsA selfCentralizingFusionData_J4

theorem benderBranch
    : BenderBranch :=
  benderBranch_of_tits titsNoStronglyClosedElemAbelian titsSylowCentralizingAutInner

end CFSG.QuasithinUnique
