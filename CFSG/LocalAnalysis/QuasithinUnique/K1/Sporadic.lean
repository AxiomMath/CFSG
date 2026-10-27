module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicCases
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicSelfCentral
public import CFSG.Sporadic.J4

public section

namespace CFSG.QuasithinUnique.K1

open CFSG.Blueprint.NativeSporadic

theorem k1_sporadic_of_noStronglyClosed
    (hJ4 : NoStronglyClosedElemAbelian (Carrier .J4)) :
    K1FamilyRecognition SporadicFamilyCat :=
  k1_sporadic_cases CFSG.Sporadic.J4.fam_j4_simplicity.2.2 hJ4

theorem k1_sporadic
    (hJ4 : SelfCentralizingFusionData (Carrier .J4)) :
    K1FamilyRecognition SporadicFamilyCat := by
  have : Finite (Carrier .J4) := CFSG.Sporadic.J4.fam_j4_simplicity.1
  exact k1_sporadic_of_noStronglyClosed
    (noStronglyClosedElemAbelian_of_selfCentralizingFusionData hJ4)

end CFSG.QuasithinUnique.K1
