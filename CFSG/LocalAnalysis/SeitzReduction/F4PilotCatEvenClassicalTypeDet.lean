module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDet

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Assembly

theorem catSp6EvenOuter_of_exceptional_families_holds
    (hG2 : CatSp6EvenOuterFamily .G2) (hF4 : CatSp6EvenOuterFamily .F4)
    (hE6 : CatSp6EvenOuterFamily .E6) (hE7 : CatSp6EvenOuterFamily .E7)
    (hE8 : CatSp6EvenOuterFamily .E8) (h2E6 : CatSp6EvenOuterFamily .twistedE6)
    (h3D4 : CatSp6EvenOuterFamily .trialityD4) : CatSp6EvenOuter :=
  catSp6EvenOuter_of_exceptional_families lieModel_PSp_three_two_unique_classicalOrSuzuki hG2 hF4 hE6 hE7 hE8 h2E6 h3D4

end Assembly

end CFSG.SeitzReduction.F4Pilot
