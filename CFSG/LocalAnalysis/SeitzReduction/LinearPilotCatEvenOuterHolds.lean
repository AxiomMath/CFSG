module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterExc
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterOmega

public section

namespace CFSG.SeitzReduction.LinearPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem catSLmEvenOuterAt_of_typeDet {m : ℕ} (hm : 3 ≤ m) (hdet : SLmEvenTypeDetAt m) :
    CatSLmEvenOuterAt m :=
  catSLmEvenOuterAt_of_open_families (catSLmEvenOuterFamilyAt_PSL hm hdet)
    (catSLmEvenOuterFamilyAt_PSU hm hdet) (catSLmEvenOuterFamilyAt_PSp hm hdet)
    (catSLmEvenOuterFamilyAt_POmegaPlus hm hdet) (catSLmEvenOuterFamilyAt_POmegaMinus hm hdet)
    (catSLmEvenOuterFamilyAt_G2 hm hdet) (catSLmEvenOuterFamilyAt_F4 hm hdet)
    (catSLmEvenOuterFamilyAt_E6 hm hdet) (catSLmEvenOuterFamilyAt_E7 hm hdet)
    (catSLmEvenOuterFamilyAt_E8 hm hdet) (catSLmEvenOuterFamilyAt_twistedE6 hm hdet)
    (catSLmEvenOuterFamilyAt_trialityD4 hm hdet)

end CFSG.SeitzReduction.LinearPilot
