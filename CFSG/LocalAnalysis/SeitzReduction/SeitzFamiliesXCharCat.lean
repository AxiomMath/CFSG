module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotHR8Final
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAssembly
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatOmegaMinus
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Small

theorem slmCatalogueClausesAt_of_xchar {m : ℕ} (hm : 3 ≤ m)
    (hdet : LinearPilot.SLmEvenTypeDetAt m) (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : LinearPilot.CatSLmSporadicAt m) : LinearPilot.SLmCatalogueClausesAt m :=
  LinearPilot.slmCatalogueClausesAt_of_inputs hm hdet hGLS
    (CrossChar.sLmNotOddLieInputAt (by omega)) hSpor

theorem sumCatalogueClausesAt_of_xchar {m : ℕ} (hm : 4 ≤ m) (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : UnitaryPilot.CatSUmSporadicAt m) : UnitaryPilot.SUmCatalogueClausesAt m :=
  UnitaryPilot.sumCatalogueClausesAt_of_inputs hm hGLS (CrossChar.sUmNotOddLieInputAt m) hSpor

theorem omegaCatalogueClausesAt_of_xchar {m : ℕ} (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : OmegaPilot.CatOmegaSporadicAt m) : OmegaPilot.OmegaCatalogueClausesAt m :=
  OmegaPilot.omegaCatalogueClausesAt_of_inputs hGLS (CrossChar.omegaNotOddLieInputAt m) hSpor

end Small

section Large

theorem sp2mCatalogueClausesAt_of_xchar (hGLS : GLS3OddLieAutComponentsInput) {m : ℕ}
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (hres : SymplecticPilot.CatSp2mSporadicResidual m) :
    SymplecticPilot.Sp2mCatalogueClausesAt m :=
  SymplecticPilot.sp2mCatalogueClausesAt_of_inputs hGLS (CrossChar.sp2mNotOddLieInput m) hMinn
    hMcomp hres

theorem sp6CatalogueClauses_of_xchar (hGLS : GLS3OddLieAutComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput)
    (hres : F4Pilot.CatSp6SporadicResidual) : F4Pilot.Sp6CatalogueClauses :=
  F4Pilot.sp6CatalogueClauses_of_inputs (F4Pilot.catSp6EvenOuter_of_exceptional_families_holds
      F4Pilot.catSp6EvenOuterFamily_G2 F4Pilot.catSp6EvenOuterFamily_F4
      F4Pilot.catSp6EvenOuterFamily_E6 F4Pilot.catSp6EvenOuterFamily_E7
      F4Pilot.catSp6EvenOuterFamily_E8 F4Pilot.catSp6EvenOuterFamily_twistedE6
      F4Pilot.catSp6EvenOuterFamily_trialityD4) hGLS
    CrossChar.sp6NotOddLieInput hMinn hMcomp hres

theorem e7CatalogueClauses_of_xchar_monster (hGLS : GLS3OddLieAutComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput) :
    E8Pilot.E7CatalogueClauses :=
  E8Pilot.e7CatalogueClauses_of_leafInputs hGLS CrossChar.e7NotOddLieInput hMinn hMcomp

theorem omegaCatalogueClausesAt_four_of_xchar (hGLS : GLS3OddLieAutComponentsInput)
    (hMinn : MonsterInnerInput) (hMcomp : MonsterLocalComponentsInput) :
    OmegaPilot.OmegaCatalogueClausesAt 4 :=
  TwistedE6Pilot.omegaCatalogueClausesAt_four_of_leafInputs hGLS
    (CrossChar.omegaNotOddLieInputAt 4) hMinn hMcomp

end Large

end CFSG.SeitzReduction
