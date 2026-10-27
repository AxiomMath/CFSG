module

public import CFSG.GH74.GLS.Stage12.Stage1Master
public import CFSG.GH74.GLS.Stage12.Stage2Master
public import CFSG.GH74.GLS.Stage2.Final.Top
public import CFSG.GH74.GLS.Stage2.Final.ModelCenter
public import CFSG.GH74.GLS.Stage2.Final.ModelOdd
public import CFSG.GH74.GLS.Stage2.Final.ModelDisjoint
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass
public import CFSG.GH74.GLS.Stage2.Final.ModelLayerBar
public import CFSG.GH74.GLS.Stage2.Final.Thm4.CoverGriess
public import CFSG.GH74.GLS.Stage2.Final.ECInterGriess
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.M12L144
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Final
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7SylowLeaf
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1Std
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2K1C3
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91Proof
public import CFSG.GH74.Uniqueness.SU.SU13Bridge
public import CFSG.GH74.Uniqueness.SU.SU13Main9
public import CFSG.GH74.Uniqueness.SU.KI7dMain
public import CFSG.GH74.Uniqueness.SU.SU13Final
public import CFSG.ClassicalInvolution.Asc77.AscT3TypedG2GenMax
public import CFSG.GH74.GLS.C3.Layer1.St1P720Top2
public import CFSG.GH74.GLS.C3.Layer1.St1RigTop
public import CFSG.GH74.GLS.C3.Layer1.Th2L625c2
public import CFSG.GH74.GLS.IVK.KI2
public import CFSG.GH74.GLS.IVK.LiftedProofs
public import CFSG.GH74.GLS.IVK.LiftedProofs3
public import CFSG.GH74.GLS.IVK.LiftedProofs4
public import CFSG.GH74.GLS.IVK.LiftedProofs5
public import CFSG.GH74.GLS.IVK.LiftedProofs6
public import CFSG.GH74.GLS.IVK.LiftedProofs7
public import CFSG.GH74.GLS.IVK.LiftedProofsSec7
public import CFSG.GH74.GLS.IVK.Proofs2.LocalUnbalancing
public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55Even
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Ext
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyStarThm
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Coprime
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L126Cov1
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Final
public import CFSG.GH74.GLS.Stage4.T2LeafC
public import CFSG.GH74.GLS.Stage4.T2OddAut
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T6Basic
public import CFSG.GH74.GLS.Stage4.T6Defs
public import CFSG.GroupTheory.ThompsonIsomorphism
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.Milestones.ZJ_glauberman_characteristic
public import CFSG.Models.PGLOrders
public import CFSG.Models.PGLSimple
public import CFSG.Monster.Existence.Defs
public import CFSG.RankThree.Chevalley.SteinbergBTThreeG2Subfield
public import CFSG.RankThree.PartOne.KC.SymplecticSubfield
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec16.Item162Res7ProofAlt
public import CFSG.Sporadic.Ly.ThreeBSpec
public import CFSG.Sporadic.Recognition.LyonsAS44Quat
public import CFSG.Sporadic.Recognition.LyonsLocalEdge
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.J4SThree
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.StronglyEmbedded.SteinbergCDOddOrderStableActions
public import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.GH74.GLS.Stage12

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Glue

structure M12Leaves : Prop where
  std : IV3K1LeafStd
  c3 : IV3K1LeafC3

structure ClassicalLeaves : Prop where
  ecInter : Stage2.Final.ECInter

theorem ClassicalLeaves.toFacts (L : ClassicalLeaves) : Stage2.Final.ClassicalData :=
  ⟨Stage2.Final.modelCenter, Stage2.Final.modelOddCore, Stage2.Final.modelOneClass, Stage2.Final.modelsDisjoint,
    Stage2.Final.modelLayerBar, L.ecInter⟩

structure Stage12LeavesB : Prop where
  stage1 : Stage1Leaves
  m12 : M12Leaves
  stage2 : Stage2Leaves

namespace Stage12LeavesB

theorem thm231 (_L : Stage12LeavesB)
    : Uniqueness.SU.SU13.Thm231Stmt := Uniqueness.SU.SU13.thm231_of_ki8c Uniqueness.SU.K.ki8c

variable (L : Stage12LeavesB)

include L

theorem stage4_of (hRG : Stage1.Main.RankG2) (hcov : Stage2.Final.Thm4.PSp4_oddCover)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage4_Std :=
  Stage2.Final.s_stage4_Std_of_stage12
    L.m12.std.sylowStd
    (fun _ _ _ _ _ _ Kb => iv3SylowLeafA7_of (ivkA7Facts_of_proved IVK.ivk_1_1f) Kb) Sec14.IVK91Proof.ivk_9_1_proved (Prod.lemma14_4 Sec14.IVK91Proof.ivk_9_1_proved)
    (Prod.lemma14_5_thm (Prod.lemma14_4 Sec14.IVK91Proof.ivk_9_1_proved))
    (L.stage1.stage1_out_three_of hRG) (L.stage2.main hcov hGA)

theorem stage4 (hcov : Stage2.Final.Thm4.PSp4_oddCover)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage4_Std :=
  L.stage4_of Stage1.Main.rankG2_thm hcov hGA

theorem stage2Four_of
    (hRG : Stage1.Main.RankG2) (hcov : Stage2.Final.Thm4.PSp4_oddCover)
    (hEC : Stage2.Final.ECInter)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage2Four_Std :=
  Stage2.Final.s_stage2Four_Std_of_stage12 (Uniqueness.SU.SU13.s_noTwoAnNineTen_of_ki8bc Uniqueness.SU.K.ki8b Uniqueness.SU.K.ki8c)
    (ClassicalLeaves.toFacts ⟨hEC⟩)
    (L.stage1.stage1_out_four_of hRG) (L.stage2.main hcov hGA)

theorem stage2Four (hcov : Stage2.Final.Thm4.PSp4_oddCover) (hEC : Stage2.Final.ECInter)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage2Four_Std :=
  L.stage2Four_of Stage1.Main.rankG2_thm hcov hEC hGA

theorem main (hcov : Stage2.Final.Thm4.PSp4_oddCover) (hEC : Stage2.Final.ECInter)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage4_Std ∧ S_stage2Four_Std := ⟨L.stage4 hcov hGA, L.stage2Four hcov hEC hGA⟩

theorem main_of_griess (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : S_stage4_Std ∧ S_stage2Four_Std :=
  L.main (Stage2.Final.Thm4.psp4_oddCover_of_griess hGA)
    (Stage2.Final.ECInterGriess.ecInter_of_griess hGA
      (L.stage2.main (Stage2.Final.Thm4.psp4_oddCover_of_griess hGA) hGA)) hGA

end Stage12LeavesB

end CFSG.GH74.GLS.Stage12
