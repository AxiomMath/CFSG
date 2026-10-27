module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalThree
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatSporadicResidual
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Mason2
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphRowParam
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalRankOne

public section

namespace CFSG.SeitzReduction

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

section Base

section RankOne

theorem seitzRankOneExclusion_of_final4 (hU : RankOne.RankOneUnitaryExclusion)
    (hC1 : RankOne.SzC1ExclusionData) : SeitzRankOneExclusion :=
  seitzRankOneExclusion_of_final RankOne.gms43MasonInput hU hC1

end RankOne

section Mid

section Residual

theorem catSp6SporadicResidualAtF_one_holds : CatSp6SporadicResidualAtF 1 :=
  catSp6SporadicResidual_iff_forall_atF.1 SporadicRefine.catSp6SporadicResidual_holds 1

theorem catSp2mSporadicResidualAtF_three_one_holds :
    SymplecticPilot.CatSp2mSporadicResidualAtF 3 1 :=
  catSp2mSporadicResidualAtF_three_of_sp6 catSp6SporadicResidualAtF_one_holds

theorem forall_catSp2mSporadicResidual_holds :
    ∀ m : ℕ, 3 ≤ m → SymplecticPilot.CatSp2mSporadicResidual m :=
  forall_catSp2mSporadicResidual_of_atF_three_one catSp2mSporadicResidualAtF_three_one_holds

section F4

theorem seitzExclusion_highF4_of_final4 (hGLS : GLS3OddLieAutComponentsInput)
    (hSN : F4Pilot.E6GraphRowSpinNormInput) (hTD : F4Pilot.TwistedE6GraphRowDInput)
    (h2 : F4Pilot.TwoRowsInput) : SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_final3 hGLS catSp6SporadicResidualAtF_one_holds
    (F4Pilot.e6RowCTQuotInput_of_spinNorm hSN) F4Pilot.e6RowXiCaseLInput_holds
    (F4Pilot.twistedE6RowCTQuotInput_of_dInput hTD) F4Pilot.twistedE6RowXiCaseLInput_holds h2

section Big

theorem seitzExclusion_highPSp_of_final4 (hGLS : GLS3OddLieAutComponentsInput)
    (hGraph : SymplecticPilot.SpGraphRowsInput) (hThree : SymplecticPilot.SpThreeInput)
    (hTwo : SymplecticPilot.SpTwoInput) : SeitzExclusion HighPSp :=
  seitzExclusion_highPSp_of_final3 hGLS catSp2mSporadicResidualAtF_three_one_holds hGraph hThree
    hTwo

end Big

end F4

end Residual

end Mid

end Base

end CFSG.SeitzReduction
