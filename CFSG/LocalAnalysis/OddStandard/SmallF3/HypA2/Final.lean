module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FinalPhases
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrime
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP4
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP5
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpHolds
public import CFSG.LocalAnalysis.ComponentClassification.GS82L34P11
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Final
public import CFSG.GH74.GLS.C3.Layer1.St1RigTop
public import CFSG.GH74.GLS.C3.Layer1.PU4Proved
public import CFSG.Milestones.CT_rank_two_standard_recognition_frontier
public import CFSG.Milestones.CT_even_small_Lie_standard_frontier
public import CFSG.Milestones.CL_LIT_classical_involution_theorem

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification _root_.Certificates

theorem phaseInputs_holds
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hHarris : HarrisLit.Harris82Theorem1SimpleKProperOdd) (hChevOdd : ChevOddInChev2) :
    Phase1Inputs ∧ Phase2Inputs := by
  refine ⟨?_, ?_⟩
  · exact
    { dPrime := GS82PumpInputs.theoremDPrime_holds
      p1 := GS82PumpInputs.chevOddPumpLeaf_holds
      p2 := GS82PumpInputs.chevOddCentralPumpInput_holds
      p4 := GS82PumpInputs.mTypeOfSLTwoSection_holds
      p5 := GS82PumpInputs.altCentralPumpInput_holds
      p7 := GS82PumpInputs.sLTwoCentralPumpInput_holds
      p8 := GS82PumpInputs.spFourThreeCentralPumpInput_holds
      p11 := GS82PumpInputs.l34CentralSLTwoFact_holds
      griess := TBLit.GriessMultipliersOdd.of_allModels TBLit.griessMultipliersAllModels_holds
      schur := CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
      solomon := CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
        (@CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models)
      harris := hHarris
      noSL2 := fun G _ _ _ => HarrisLit.T1.false_of_intrinsic_slTwo hCIT
      classical := fun X _ _ _ => FooteLit.oddLieType_of_classical_twoComponent hCIT
      chevOdd := hChevOdd }
  · exact
    { bIg := CFSG.GH74.GLS.b_ig_6_10_proved
      bPU4 := CFSG.GH74.GLS.b_cor_PU4_proved
      rankTwo := CFSG.Milestones.ct_rank_two_standard_recognition_frontier_models
      smallLie := CFSG.Milestones.ct_even_small_lie_standard_frontier_models
      quat := fun hC G _ _ L hS S r hr e =>
        CFSG.OddStandard.quaternion_oddLie_or_M12 hC hS S hr e
      dihedral := CFSG.Milestones.lr_dihedral_simple_recognition
      orders := fun X _ =>
        ⟨fun ⟨e⟩ => by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.He.card_He,
         fun ⟨e⟩ => by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.Mathieu.card_M12,
         fun ⟨e⟩ => by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.J2.card_J2,
         fun ⟨e⟩ => by rw [Nat.card_congr e.toEquiv]; exact CFSG.Sporadic.HS.card_HS⟩
      g2Four := fun X _ h =>
        (CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
          (CFSG.Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel (t := .G2) (by decide)
            h)).trans (by decide : CFSG.Open.ordG2 (2 ^ 2) = 251596800)
      a8 := fun X _ h n hn =>
        (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X
          (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) h)).2.2 (Fin n)
            (by simpa using hn)
      g2Derived := CFSG.Quasithin.EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds }

theorem smallF3OmegaV_of_inputs
    (hAlt : CFSG.OddStandard.AltStdCyclicBalancedFalse)
    (hCIT : type_of% @CFSG.Milestones.cl_lit_classical_involution_theorem_models)
    (hEven : EvenResidualStd)
    (hCTSS : CTSSStd)
    (hL2 : CFSG.Yardstones.M0362f3a873a3.OddLieThm187bResidualL2Ree)
    (hHarris : HarrisLit.Harris82Theorem1SimpleKProperOdd) (hChevOdd : ChevOddInChev2)
    (hLeaves1 : Leaves1) (hLeaves2 : Leaves2) : Omega.SmallF3OmegaV := by
  obtain ⟨hI, hP⟩ := phaseInputs_holds hCIT hHarris hChevOdd
  exact smallF3OmegaV_of_phases hAlt hCIT hEven hCTSS hL2 hI hP hLeaves1 hLeaves2

end CFSG.OddStandard.SmallF3.HypA2
