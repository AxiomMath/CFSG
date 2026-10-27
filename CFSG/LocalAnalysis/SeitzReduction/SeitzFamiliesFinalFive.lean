module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalFour
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCTField
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotUniqueFieldInput
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2PositionHolds
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllProved
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBounds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SevenSwapFinal
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34ONOuterAssembly
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeMain
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatSporadicProved

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.ComponentClassification.CatLeafProof (monsterInnerInput monsterLocalComponentsInput)

@[expose] def TwistedE6TwoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ¬ LieModel L .twistedE6 0 2 1

@[expose] def OmegaPlusHigherRankRigidityInput : Prop :=
  ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hn : 5 ≤ n), Even f →
      OmegaPilot.HigherRankCoresRigid n K
        (OmegaPilot.plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn)

theorem omegaPlusResidualMatrixInput_of_higherRank (h : OmegaPlusHigherRankRigidityInput) :
    OmegaPilot.OmegaPlusResidualMatrixInput :=
  OmegaPilot.omegaPlusResidualMatrixInput_of_nonFieldCoresRigid fun n f K _ _ _ hK hn hfe =>
    OmegaPilot.nonFieldCoresRigid_plus_of_higherRankCoresRigid hK hn (h n f K hK hn hfe)

section Base

section E8

theorem seitzExclusion_highTwistedE6_of_final5 (hGLS : GLS3OddLieAutComponentsInput)
    (h2 : TwistedE6TwoInput) : SeitzExclusion (HighExceptional .twistedE6) := by
  intro G _ _ L hset ⟨f, hL⟩
  obtain ⟨hf, -⟩ := TwistedE6Pilot.exists_mulEquiv_graphFixedRootGroup_of_lieModel hL
  rcases Nat.lt_or_ge f 2 with h1 | hf2
  · obtain rfl : f = 1 := by omega
    exact h2 G L hset hL
  · exact TwistedE6Pilot.false_of_seitzSetting_twistedE6_of_inputs hGLS
      (CrossChar.sUmNotOddLieInputAt 6) (CrossChar.omegaNotOddLieInputAt 4) monsterInnerInput
      monsterLocalComponentsInput TwistedE6Pilot.ctFieldFamilyInput2E6_holds
      TwistedE6Pilot.uniqueFieldInput2E6_holds hset hf2 hL

section E7

theorem seitzExclusion_highPOmegaMinus_of_final5 (hGLS : GLS3OddLieAutComponentsInput)
    (h4 : OmegaPilot.OmegaMinusFourInput) (h2 : OmegaPilot.OmegaMinusTwoInput) :
    SeitzExclusion HighPOmegaMinus :=
  OmegaPilot.seitzExclusion_highPOmegaMinus_of_centralizer_of_five_le h4 h2
    (fun m _ => omegaCatalogueClausesAt_of_xchar hGLS (OmegaPilot.catOmegaSporadicAt m))
    (fun _ hn => OmegaPilot.omegaMinusInvolutionCentralizerInput_holds hn)

section PSU

theorem twistedE6TwoInput_of_rows_of_gls3 (hGLS : GLS3OddLieAutComponentsInput)
    (hF : TwistedE6Pilot.TwistedE6TwoFieldRowInput) (hS : TwistedE6Pilot.TwistedE6TwoSwapRowInput) :
    TwistedE6TwoInput :=
  fun _ _ _ _ hset hL => TwistedE6Pilot.false_of_twistedE6_two_of_rows hGLS
    UnitaryPilot.catSUmSporadicAtF_six_one hF hS hset hL

section F4

theorem seitzExclusion_highF4_of_final5 (hGLS : GLS3OddLieAutComponentsInput)
    (hTD : F4Pilot.TwistedE6GraphRowDInput) (h2 : F4Pilot.TwoRowsInput) :
    SeitzExclusion (HighExceptional .F4) :=
  seitzExclusion_highF4_of_final4 hGLS F4Pilot.e6GraphRowSpinNormInput_holds hTD h2

section PSL

theorem seitzExclusion_highPSL_of_final5 (hGLS : GLS3OddLieAutComponentsInput)
    (h56 : LinearPilot.LinearTwoFiveSixInput) : SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_final3 hGLS LinearPilot.catSLmSporadicAt_three
    (LinearPilot.linearTwoInput_of_gls3_fiveSix hGLS h56)

theorem spThreeInput_of_gls3 (hGLS : GLS3OddLieAutComponentsInput)
    (hres2 : SymplecticPilot.CatSp2mSporadicResidual 2)
    (hGraph : SymplecticPilot.SpThreeGraphRowsInput) : SymplecticPilot.SpThreeInput :=
  SymplecticPilot.spThreeInput_of_xchar hGLS monsterInnerInput monsterLocalComponentsInput hres2
    LinearPilot.catSLmSporadicAt_three hGraph

end PSL

end F4

end PSU

end E7

end E8

end Base

end CFSG.SeitzReduction
