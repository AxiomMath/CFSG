module

public import CFSG.GH74.FinalAssemblyDeep13
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1Proof
public import CFSG.GH74.GLS.C3.Layer1.Th2A7BetaFinal
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Final
public import CFSG.GH74.Generic.BProg.B2.Gate3Allow
public import CFSG.GH74.Generic.BProg.B3.DictRepair
public import CFSG.GH74.Generic.BProg.B3.DictS3
public import CFSG.GH74.Generic.BProg.B1.JPrime
public import CFSG.GH74.Generic.BProg.B3.DictS1High
public import CFSG.GH74.Generic.BProg.B3.DictS1Q3
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Bridge
public import CFSG.GH74.Generic.BProg.B3.SolvP101
public import CFSG.LocalAnalysis.OddStandard.GH71.Bridge
public import CFSG.GH74.Generic.BProg.B2.T1Done
public import CFSG.LocalAnalysis.OddStandard.GH71.S55D4Ord3Final
public import CFSG.GH74.Generic.BProg.B2.T3S1Done
public import CFSG.GH74.Generic.BProg.B2.T3Wire
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Main
public import CFSG.GH74.Generic.BProg.B3.S1Three
public import CFSG.GH74.Generic.BProg.B3.S3HLOFinal
public import CFSG.GH74.Generic.BProg.B3.S3SL2Pump
public import CFSG.GH74.Generic.BProg.B3.S45EvenN8
public import CFSG.GH74.Generic.BProg.B3.S45EvenN6
public import CFSG.GH74.Generic.BProg.B2.NoSD
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.GH74.Generic.BProg.B2.T4S1Assembly
public import CFSG.GH74.Generic.BProg.B2.Thm2Done
public import CFSG.GH74.Generic.BProg.B2.PumpupTableProved
public import CFSG.GH74.Generic.BProg.B2.T4L5InvModels
public import CFSG.GH74.Generic.BProg.B2.T4B3aG
public import CFSG.GH74.Generic.BProg.B3.KG9Main
public import CFSG.GH74.Generic.BProg.B2.T4P151G
public import CFSG.GH74.Generic.BProg.B2.T4P151L
public import CFSG.GH74.Generic.BProg.B2.T4P151P
public import CFSG.GH74.Generic.BProg.B2.T4P151V
public import CFSG.GH74.Generic.BProg.B2.T4P151W
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTProved
public import CFSG.GH74.Generic.BProg.B3.S3T2A7Close
public import CFSG.GH74.Generic.BProg.B2.T4PGVMain
public import CFSG.GH74.Generic.BProg.B2.T4PGVTMain
public import CFSG.GroupTheory.SteinbergCBFTSCN
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7FieldQuat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieDatum
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormTwE6

public section

namespace CFSG.GH74

open GLS Subgroup Blueprint Assembly.LowTwoRank

theorem milestone_forms_of_leaves35
    (hQ : S_QTKE_Gen4) :
    ModelsFormStatement ∧ OrderFormStatement :=
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hIV3 : Stage12.M12Leaves :=
    ⟨Stage1.Thm6.Glue.iv3K1LeafStd_proved, Stage1.Thm6.Glue.iv3K1LeafC3_proved⟩
  have hQ3 : Generic.BProg.B2.T4.P151V.VertQ3 :=
    Generic.BProg.B2.T4.PGV.vertQ3_of_table ComponentClassification.TBLit.griessMultipliersAllModels_holds
      Generic.BProg.B2.T4.PGV.q3Table_holds
  have h151 : Generic.BProg.B2.T4.T4S1.S1Prop151 :=
    Generic.BProg.B2.T4.P151G.s1Prop151_of_layer GLS.b_B2_g4_proved Generic.BProg.B2.stage2Thm2C_proved
      (Generic.BProg.B2.T4.P151L.layer151F_of_pumpGen3 GLS.b_B2_g4_proved
        (Generic.BProg.B2.T4.P151P.pumpGen3_of_vert ComponentClassification.TBLit.griessMultipliersAllModels_holds
          (Generic.BProg.B2.T4.P151V.pumpGenVert3_of
            ComponentClassification.TBLit.griessMultipliersAllModels_holds
            (Generic.BProg.B2.T4.P151W.vertL4_proved
              ComponentClassification.TBLit.griessMultipliersAllModels_holds)
            Generic.BProg.B2.T4.P151W.vertG2_proved hQ3)))
  have t3 : Generic.BProg.Stage2Thm3 :=
    Generic.BProg.B2.stage2Thm3_of_S1 Generic.BProg.B2.stage2Thm3S1_proved
  have t4 : Generic.BProg.Stage2Thm4 :=
    Generic.BProg.B2.T4.T4S1.stage2Thm4_of_leaves (Generic.BProg.B2.T4.B3aG.notShape3L5_of GLS.b_B2_g4_proved)
      Generic.BProg.B2.T4.L5InvModels.puL5InvE8_proved h151
      Generic.BProg.B2.PumpupOutOrders.pumpupTableU_proved Generic.BProg.B2.T4.outG2Comm_proved
      CFSG.GH74.GLS.b_B2_g4_proved Generic.BProg.B2.stage2Thm2C_proved
  have hGKF : Generic.GenericKnownFacts :=
    Generic.genericKnownFacts_of_griess CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hE2 : E2.E2ComponentFacts := E2.e2ComponentFacts
  have hNo := Generic.BProg.B2.noJPrimeNonSD
  have hEven := Generic.BProg.B3.N6_table hGKF hE2
  have hBal : Generic.BProg.Stage1Bal :=
    ⟨Generic.BProg.B3.stage1BalFor_shape1 Generic.BProg.B3.KG531BP.kg531BPairNine_proved,
      Generic.BProg.B3.stage1BalFor_shape3_of_c2' (Generic.BProg.B3.c2CoverInput_of_facts hGKF hE2) hNo
        Generic.BProg.B3.S3T2A7.hSD29_proved,
      Generic.BProg.B3.N8_stage1BalFor_shape4_ea hNo hEven,
      Generic.BProg.B3.N8_stage1BalFor_shape5_ea hNo hEven⟩
  have hA : Generic.BProg.Stage2Allow :=
    Generic.BProg.B2.stage2Allow_of_open Generic.BProg.B3.SolvP101.stage1NontrivSolv_proved hBal
      Generic.BProg.B2.stage2Thm1_proved t3 t4
  have hL1 : Generic.BProg.B_Gen4_liftJ2NS :=
    Generic.BProg.B2.b_Gen4_liftJ2NS_of_open hGA Generic.BProg.B3.SolvP101.stage1NontrivSolv_proved hBal
      Generic.BProg.B2.stage2Thm1_proved t3 t4
  have hJ' : Generic.BProg.JPrimeNS :=
    Generic.BProg.B1.jPrimeNS_of_known_facts (Generic.genericKnownFacts_of_griess hGA)
  have hN := Generic.BProg.B3.nbrComp_of_programJ hA hL1 hJ' hGA Generic.BProg.B3.dictS3J_proved
    Generic.BProg.B3.dictS1HighJ_proved Generic.BProg.B3.dictS1ThreeJ_proved Generic.BProg.B3.dictS1Q3J_proved
  milestone_forms_of_leaves13 hQ hGA hL1 hN.1 hN.2 (CFSG.GH74.GLS.b_thm2_A7_exc_of_griess hGA).1
    ⟨⟨⟨⟩, ⟨⟩⟩, hIV3,
      ⟨⟨⟩, Stage2.Signalizer.Ivk8.lemma5_5m_leaves CFSG.OddStandard.GH71.S55.d4Ord3
          CFSG.OddStandard.GH71.S55.ordPInner_fd4d CFSG.OddStandard.GH71.S55.ordPInner_freed
          CFSG.OddStandard.GH71.S55.comp5m2Types_proved CFSG.OddStandard.GH71.S55.comp5m1Types_proved
          Stage2.Signalizer.Ivk8.BT.case55b_proved,
        CFSG.OddStandard.GH71.oddCoreThreeLy_proved, ⟨⟩, ⟨⟩⟩⟩

end CFSG.GH74
