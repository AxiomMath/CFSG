module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalSeven
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapCommMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixLMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSFive
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixMFive
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixSMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRFinal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSixMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeUSevenMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6RelayMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ChainTwMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2TwistedE6CaseLMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapOmMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterNormSwap
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedPiModelFinal
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldPieceMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveFKM
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSchur
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1CornerFinal
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAssembly
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1RegularCor
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineCountU3
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineLFourFixed

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section U3C1

theorem u3C1Exclusion_of_final8 (hstar : ∀ f : ℕ, 2 ≤ f → RankOne.StarPrimeStatement f)
    (hswap : RankOne.U3C1OuterMuOneSwapInput) : RankOne.U3C1Exclusion :=
  RankOne.u3C1Exclusion_of_outer_next
    (RankOne.u3C1OuterInput_of_ncyc (RankOne.u3C1OuterNcycInput_of_sylowStage
      (RankOne.u3C1NcycSylowStageInput_of_muOne
        (RankOne.u3C1OuterMuOneInput_of_norm (RankOne.u3C1OuterMuOneNormInput_of_swap hswap))
        RankOne.u3C1OuterMuOneSylowInput_holds)
      (u3NotSylowNcycInput_of_starPrime hstar)))
    RankOne.u3C1NextInput

section U3

theorem rankOneUnitaryExclusion_of_starPrime_norm
    (hstar : ∀ f : ℕ, 2 ≤ f → RankOne.StarPrimeStatement f)
    (hswap : RankOne.U3C1OuterMuOneSwapInput) : RankOne.RankOneUnitaryExclusion :=
  RankOne.rankOneUnitaryExclusion_of_starPrime hstar (u3C1Exclusion_of_final8 hstar hswap)
    RankOne.u3SixNineFourInput_holds u3EndingInput_holds

theorem seitzRankOneExclusion_of_starPrime_norm
    (hstar : ∀ f : ℕ, 2 ≤ f → RankOne.StarPrimeStatement f)
    (hswap : RankOne.U3C1OuterMuOneSwapInput) : SeitzRankOneExclusion :=
  seitzRankOneExclusion_of_final4 (rankOneUnitaryExclusion_of_starPrime_norm hstar hswap)
    RankOne.szC1ExclusionData_holds

end U3

end U3C1

section E6Row

theorem twoE6PairInput_of_final8 (hR : F4Pilot.TwoE6RelayEdgeInput) : F4Pilot.TwoE6PairInput :=
  F4Pilot.twoE6PairInput_of_edgeInput hR

section TwistedE6Row

theorem twoTwistedE6PairInput_of_final8 (hR : F4Pilot.TwoTwistedE6RelayInput) :
    F4Pilot.TwoTwistedE6PairInput :=
  F4Pilot.twoTwistedE6PairInput_of_chainInput_holds
    (F4Pilot.twoTwistedE6ChainInput_of_relayInput hR)

section OmegaPlusFour

theorem linearTwoSwapRowAtInput_six_of_final8 (hGLS : GLS3OddLieAutComponentsInput)
    (hlab6 : LinearPilot.LinearTwoSwapLabelDualAtInput 6) :
    LinearPilot.LinearTwoSwapRowAtInput 6 :=
  linearTwoSwapRowAtInput_six_of_final7 hGLS LinearPilot.lSixSOneNotSylowInput_holds
    LinearPilot.lSixFieldNOneLiftInput_holds (LinearPilot.lSixSwapGOneInput_of_labelDual hlab6)

end OmegaPlusFour

section Two

theorem twoRowsInput_of_final8 (hGLS : GLS3OddLieAutComponentsInput)
    (hRE : F4Pilot.TwoE6RelayEdgeInput) (hRT : F4Pilot.TwoTwistedE6RelayInput) :
    F4Pilot.TwoRowsInput :=
  twoRowsInput_of_cat_of_gls3 hGLS
    (F4Pilot.twoRowsCatInput_of_rows F4Pilot.twoFieldPairInput_holds F4Pilot.twoSwapPairInput_holds
      (twoE6PairInput_of_final8 hRE) (twoTwistedE6PairInput_of_final8 hRT))

theorem seitzExclusion_highF4_of_final8 (hGLS : GLS3OddLieAutComponentsInput)
    (hRE : F4Pilot.TwoE6RelayEdgeInput) (hRT : F4Pilot.TwoTwistedE6RelayInput) :
    SeitzExclusion (HighExceptional .F4) :=
  F4Pilot.seitzExclusion_highF4_of_gls3_twoRows hGLS (twoRowsInput_of_final8 hGLS hRE hRT)

theorem sp2mCatalogueClausesAt_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    ∀ m : ℕ, 3 ≤ m → SymplecticPilot.Sp2mCatalogueClausesAt m :=
  fun m hm => sp2mCatalogueClausesAt_of_xchar hGLS
    ComponentClassification.CatLeafProof.monsterInnerInput
    ComponentClassification.CatLeafProof.monsterLocalComponentsInput
    (forall_catSp2mSporadicResidual_holds m hm)

section OmegaPlus

theorem seitzExclusion_highPOmegaPlus_of_final8 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion HighPOmegaPlus :=
  seitzExclusion_highPOmegaPlus_of_final7 hGLS OmegaPilot.plusFourSwapCommInput_holds
    OmegaPilot.omegaPlusTwoTenFieldGlobalInput_holds

theorem seitzExclusion_highPOmegaMinus_of_final8 (hGLS : GLS3OddLieAutComponentsInput) :
    SeitzExclusion HighPOmegaMinus :=
  seitzExclusion_highPOmegaMinus_of_final7 hGLS OmegaPilot.omegaMinusTwoTenFieldGlobalInput_holds

section PSp

theorem slmCatalogueClausesAt_three_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    LinearPilot.SLmCatalogueClausesAt 3 :=
  slmCatalogueClausesAt_of_xchar le_rfl (LinearPilot.slmEvenTypeDetAt le_rfl) hGLS
    LinearPilot.catSLmSporadicAt_three

theorem spThreeGraphRowsInput_of_final8 (hGLS : GLS3OddLieAutComponentsInput)
    (hLOs : SymplecticPilot.SpThreeLinearOddStandardInput)
    (hLOt : SymplecticPilot.SpThreeLinearOddTrivialSiegelInput)
    (hUOo : SymplecticPilot.SpThreeUnitaryOddOrthInput)
    (hUOa : SymplecticPilot.SpThreeUnitaryOddSiegelAlignInput) :
    SymplecticPilot.SpThreeGraphRowsInput :=
  spThreeGraphRowsInput_of_final7 hGLS
    (SymplecticPilot.spThreeUnitaryEvenRecognitionInput_of_catalogue
      (slmCatalogueClausesAt_three_of_gls3 hGLS))
    (SymplecticPilot.spThreeKindCoverInput_linearOdd_of_clauses
      (slmCatalogueClausesAt_three_of_gls3 hGLS) (LinearPilot.slmEvenTypeDetAt le_rfl) hLOs hLOt)
    (SymplecticPilot.spThreeKindCoverInput_unitaryOdd_of_orth_align
      (slmCatalogueClausesAt_three_of_gls3 hGLS) (LinearPilot.slmEvenTypeDetAt le_rfl) hUOo hUOa)

section LFive

theorem linearTwoSwapRowAtInput_five_of_final8 (hGLS : GLS3OddLieAutComponentsInput)
    (hsyl5 : LinearPilot.LFiveSOneSylowPartInput)
    (hlab5 : LinearPilot.LinearTwoSwapLabelDualAtInput 5) :
    LinearPilot.LinearTwoSwapRowAtInput 5 :=
  LinearPilot.linearTwoSwapRowAtInput_five_of_swap (slmCatalogueClausesAt_four_of_gls3 hGLS)
    (LinearPilot.slmEvenTypeDetAt (by norm_num)) SporadicRefine.sporadicFixedLFourTwoInput
    LinearPilot.lFiveNormalizerPointRadicalInput
    (LinearPilot.lFiveNotNormalSwapInput_of_notSylow (LinearPilot.lFiveSOneNotSylowSwapInput_of_core
      (LinearPilot.lFiveSOneNotSylowCoreInput_of_sylowPart hsyl5)))
    (fun _ _ hX => LinearPilot.oddSchurTrivial_of_lieModel_PSL_four_four hX)
    LinearPilot.lFiveFieldNOneLiftInput_holds (LinearPilot.lFiveSwapGOneInput_of_labelDualAt hlab5)

end LFive

end PSp

end OmegaPlus

end Two

end TwistedE6Row

end E6Row

end CFSG.SeitzReduction
