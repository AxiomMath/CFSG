module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSL
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSU
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalPSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalOmega

public section

namespace CFSG.SeitzReduction.F4Pilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Classical


theorem catSp6EvenOuterFamily_classical (hdet : Sp6EvenTypeDet) :
    CatSp6EvenOuterFamily .PSL ∧ CatSp6EvenOuterFamily .PSU ∧ CatSp6EvenOuterFamily .PSp ∧
      CatSp6EvenOuterFamily .POmegaPlus ∧ CatSp6EvenOuterFamily .POmegaMinus :=
  ⟨catSp6EvenOuterFamily_PSL hdet, catSp6EvenOuterFamily_PSU hdet,
    catSp6EvenOuterFamily_PSp hdet, catSp6EvenOuterFamily_POmegaPlus hdet,
    catSp6EvenOuterFamily_POmegaMinus hdet⟩

end Classical

section Assembly


theorem catSp6EvenOuter_of_exceptional_families (hdet : Sp6EvenTypeDet)
    (hG2 : CatSp6EvenOuterFamily .G2) (hF4 : CatSp6EvenOuterFamily .F4)
    (hE6 : CatSp6EvenOuterFamily .E6) (hE7 : CatSp6EvenOuterFamily .E7)
    (hE8 : CatSp6EvenOuterFamily .E8) (h2E6 : CatSp6EvenOuterFamily .twistedE6)
    (h3D4 : CatSp6EvenOuterFamily .trialityD4) : CatSp6EvenOuter := by
  obtain ⟨hPSL, hPSU, hPSp, hOp, hOm⟩ := catSp6EvenOuterFamily_classical hdet
  exact catSp6EvenOuter_of_open_families hPSL hPSU hPSp hOp hOm hG2 hF4 hE6 hE7 hE8 h2E6 h3D4

end Assembly

end CFSG.SeitzReduction.F4Pilot
