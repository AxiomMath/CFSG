module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalSix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeANTFinal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWFinal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTEightAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUFourAlign
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlSiegelGLS
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelOPMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNonembedMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBFinal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightRigidMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTriality
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightDichMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightParamAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightAutMain
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenConj
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingPencilNF
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveGSyl
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveESix
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixWMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNodeMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaRows

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

theorem omegaPlusSpLeviTypeANSubTwoInput_holds : OmegaPlusSpLeviTypeANSubTwoInput :=
  OmegaPilot.typeA_nSubTwo_input

theorem omegaPlusSpLeviTypeBCInput_holds : OmegaPlusSpLeviTypeBCInput :=
  fun n f K _ _ _ hK hn hfe s hss hℓ hW =>
    OmegaPilot.exists_conj_spLeviData_typeBC n f K hK hn hfe s hss hℓ hW

theorem omegaPlusHigherRankRigidityInput_holds : OmegaPlusHigherRankRigidityInput :=
  omegaPlusHigherRankRigidityInput_of_spLeviConj
    (omegaPlusSpLeviConjInput_of_typeA_nSubTwo_of_typeBC omegaPlusSpLeviTypeANSubTwoInput_holds
      omegaPlusSpLeviTypeBCInput_holds)

theorem omegaPlusResidualMatrixInput_holds : OmegaPilot.OmegaPlusResidualMatrixInput :=
  omegaPlusResidualMatrixInput_of_higherRank omegaPlusHigherRankRigidityInput_holds

section U3Ending

theorem u3EndingInput_holds : RankOne.U3EndingInput :=
  RankOne.u3EndingInput_of_sylow RankOne.u3EndingSylowInput_holds

section U3C1

theorem u3NotSylowNcycInput_of_starPrime (hstar : ∀ f : ℕ, 2 ≤ f → RankOne.StarPrimeStatement f) :
    RankOne.U3NotSylowNcycInput := fun _ _ _ _ f _ _ _ h _ hR _ =>
  h.not_isSylow_S₁_of_starPrime (hstar f h.two_le) hR

end U3C1

end U3Ending

section Rows

section Two

theorem omegaPlusTwoInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hglob : OmegaPilot.OmegaPlusTwoTenFieldGlobalInput) : OmegaPilot.OmegaPlusTwoInput :=
  OmegaPilot.omegaPlusTwoInput_of_ten_cat
    (OmegaPilot.omegaPlusTwoTenInput_of_gls3_global hGLS hglob)
    (fun m _ => OmegaPilot.omegaCatalogueClausesAt_of_gls3 hGLS m)

theorem omegaMinusTwoInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hglob : OmegaPilot.OmegaMinusTwoTenFieldGlobalInput) : OmegaPilot.OmegaMinusTwoInput :=
  OmegaPilot.omegaMinusTwoInput_of_ten_cat
    (OmegaPilot.omegaMinusTwoTenInput_of_gls3_global hGLS hglob)
    (fun m _ => OmegaPilot.omegaCatalogueClausesAt_of_gls3 hGLS m)

end Two

section Catalogue

theorem slmCatalogueClausesAt_four_of_gls3 (hGLS : GLS3OddLieAutComponentsInput) :
    LinearPilot.SLmCatalogueClausesAt 4 :=
  slmCatalogueClausesAt_of_xchar (by norm_num) (LinearPilot.slmEvenTypeDetAt (by norm_num)) hGLS
    (LinearPilot.catSLmSporadicAt_of_four_le le_rfl)

theorem spGraphRowsInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput) :
    SymplecticPilot.SpGraphRowsInput :=
  SymplecticPilot.spGraphRowsInput_of_kindCover
    (SymplecticPilot.spKindCoverInput_linearEven_of_catalogue
      (slmCatalogueClausesAt_four_of_gls3 hGLS))
    (SymplecticPilot.spKindCoverInput_unitaryEven_of_paramCT
      (SymplecticPilot.spUnitaryParamCTInput_of_catalogue
        (slmCatalogueClausesAt_four_of_gls3 hGLS)))
    (SymplecticPilot.spKindCoverInput_linearOdd_of_catalogue
      (slmCatalogueClausesAt_four_of_gls3 hGLS))
    (SymplecticPilot.spKindCoverInput_unitaryOdd_of_paramCT
      (SymplecticPilot.spUnitaryOddParamCTInput_of_catalogue
        (slmCatalogueClausesAt_four_of_gls3 hGLS)))
    SymplecticPilot.unitaryEvenInnerTwoPart_holds
    (SymplecticPilot.spOmegaPlusRowInput_of_unique
      (SymplecticPilot.spOmegaRowUniqueInput_omegaPlus_of_gls3 hGLS
        SymplecticPilot.omegaMinusNonembeddingDataInput_holds
        SymplecticPilot.omegaLagrangianATwoModelInput_holds))
    (SymplecticPilot.spOmegaMinusRowInput_of_pieces_of_unique
        SymplecticPilot.spOmegaMinusPieceInput_holds
        (SymplecticPilot.spOmegaRowUniqueInput_omegaMinus_of_gls3 hGLS))

theorem linearTwoSwapRowAtInput_six_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hsyl6 : LinearPilot.LSixSOneNotSylowInput) (hlift6 : LinearPilot.LSixFieldNOneLiftInput)
    (hG16 : LinearPilot.LSixSwapGOneInput) : LinearPilot.LinearTwoSwapRowAtInput 6 :=
  LinearPilot.linearTwoSwapRowAtInput_six_of_notNormal
    (LinearPilot.slmCatalogueClausesAt_five_of_gls3 hGLS)
    (LinearPilot.slmEvenTypeDetAt (by norm_num))
    (LinearPilot.lSixNOneNotNormalInput_of_notSylow hsyl6) hlift6
    (LinearPilot.lSixSwapNOneInput_of_gOne hG16)

theorem omegaPlusFourInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hcomm4 : OmegaPilot.PlusFourSwapCommInput) : OmegaPilot.OmegaPlusFourInput :=
  OmegaPilot.omegaPlusFourInput_of_catalogue_four OmegaPilot.omegaPlusFourResidualInput
    (slmCatalogueClausesAt_four_of_gls3 hGLS) OmegaPilot.omegaPlusFourUniqueInput_holds
    OmegaPilot.omegaPlusFourEndInput_holds (OmegaPilot.omegaPlusFourSwapInput_of_swapComm hcomm4)

section OmegaMinusFour

theorem omegaMinusFourInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput) :
    OmegaPilot.OmegaMinusFourInput :=
  OmegaPilot.omegaMinusFourInput_of_catalogue_five OmegaPilot.omegaMinusFourSwapRowInput_holds
    OmegaPilot.omegaMinusFourUniqueInput_holds OmegaPilot.omegaMinusFourEndInput_holds
    (sumCatalogueClausesAt_of_xchar le_rfl hGLS (UnitaryPilot.catSUmSporadicAt le_rfl))
    (slmCatalogueClausesAt_four_of_gls3 hGLS)

section Omega

theorem seitzExclusion_highPOmegaPlus_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hcomm4 : OmegaPilot.PlusFourSwapCommInput)
    (hglob : OmegaPilot.OmegaPlusTwoTenFieldGlobalInput) : SeitzExclusion HighPOmegaPlus :=
  OmegaPilot.seitzExclusion_highPOmegaPlus_of_open_five (omegaPlusFourInput_of_final7 hGLS hcomm4)
    (omegaPlusTwoInput_of_final7 hGLS hglob)
    (fun m _ => omegaCatalogueClausesAt_of_xchar hGLS (OmegaPilot.catOmegaSporadicAt m))
    omegaPlusResidualMatrixInput_holds
    (fun n K _ _ _ hq hn => by
      obtain ⟨f, hK⟩ := OmegaPilot.exists_card_eq_two_pow (K := K)
      exact OmegaPilot.swapPairExclusion_coordinatePlus
        ((LinearPilot.four_le_card_iff_two_le hK).1 hq) hK hn)
    (fun _ hn => OmegaPilot.omegaPlusLinearInvolutionInput_holds hn)

theorem seitzExclusion_highPOmegaMinus_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hglob : OmegaPilot.OmegaMinusTwoTenFieldGlobalInput) : SeitzExclusion HighPOmegaMinus :=
  seitzExclusion_highPOmegaMinus_of_final5 hGLS (omegaMinusFourInput_of_final7 hGLS)
    (omegaMinusTwoInput_of_final7 hGLS hglob)

section PSp

theorem spThreeGraphRowsInput_of_final7 (hGLS : GLS3OddLieAutComponentsInput)
    (hUE : SymplecticPilot.SpThreeUnitaryEvenRecognitionInput)
    (hLO : SymplecticPilot.SpThreeKindCoverInput .linearOdd)
    (hUO : SymplecticPilot.SpThreeKindCoverInput .unitaryOdd) :
    SymplecticPilot.SpThreeGraphRowsInput :=
  SymplecticPilot.spThreeGraphRowsInput_of_recognitionInputs
    (SymplecticPilot.spThreeLinearEvenRecognitionInput_of_catalogue
      (slmCatalogueClausesAt_of_xchar le_rfl (LinearPilot.slmEvenTypeDetAt le_rfl) hGLS
        LinearPilot.catSLmSporadicAt_three)) hUE hLO hUO

end PSp

end Omega

end OmegaMinusFour

end Catalogue

end Rows

end CFSG.SeitzReduction
