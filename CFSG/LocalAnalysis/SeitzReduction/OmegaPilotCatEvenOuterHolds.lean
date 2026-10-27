module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuterOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuterExc

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank


theorem catOmegaEvenOuterAt_of_typeDet {m : ℕ} (hdet : OmegaEvenTypeDetAt m) :
    CatOmegaEvenOuterAt m :=
  catOmegaEvenOuterAt_of_open_families (catOmegaEvenOuterFamilyAt_PSL hdet)
    (catOmegaEvenOuterFamilyAt_PSU hdet) (catOmegaEvenOuterFamilyAt_PSp hdet)
    (catOmegaEvenOuterFamilyAt_POmegaPlus hdet) (catOmegaEvenOuterFamilyAt_POmegaMinus hdet)
    (catOmegaEvenOuterFamilyAt_G2 hdet) (catOmegaEvenOuterFamilyAt_F4 hdet)
    (catOmegaEvenOuterFamilyAt_E6 hdet) (catOmegaEvenOuterFamilyAt_E7 hdet)
    (catOmegaEvenOuterFamilyAt_E8 hdet) (catOmegaEvenOuterFamilyAt_twistedE6 hdet)
    (catOmegaEvenOuterFamilyAt_trialityD4 hdet)

theorem catOmegaEvenOuterAt (m : ℕ) : CatOmegaEvenOuterAt m :=
  catOmegaEvenOuterAt_of_typeDet (omegaEvenTypeDetAt m)

end CFSG.SeitzReduction.OmegaPilot
