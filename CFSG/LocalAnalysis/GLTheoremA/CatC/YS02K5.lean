module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02K2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02K4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS02Rows2
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4G
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieD4Two
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2E
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieTD4T
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4Three
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieRF4S

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Certs

theorem kdLevelFiniteLie_all
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : KDLevelFiniteLie p :=
  kdLevelFiniteLie_of_rows (kdLieRowsOpen_of_rest (kdLieRowsRest_of_rest2
    ⟨kdLieRowSp4Eight_holds, kdLieRowOmega8PlusTwo_holds, kdLieRowG2Eight_holds,
      kdLieRowTD4Two_holds, kdLieRowReeF4EightThree_holds, kdLieRowReeF4ThirtyTwoFive_holds⟩))
    p hp hp2

theorem kdLevelFiniteK_all
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hM11 : KDSporRow .M 11) (hM13 : KDSporRow .M 13) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    KDLevelFiniteK p :=
  kdLevelFiniteK_of_parts (kdLevelFiniteLie_all p hp hp2)
    (KDSpor.kdLevelFiniteSporK_all hOut hbr hM11 hM13 p)

theorem ys02_of_kdLevelK
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → KDLevelK p)
    (hM : ∀ p : ℕ, p.Prime → p ≠ 2 → ListedMultiplierBound p) (hH : HatOddMultiplierBound) :
    YS02 :=
  ys02_of_i1132_i1412
    (fun G _ _ m hctx p hp => i1132UsedAt_of_kd
        HardMathSupport.Timmesfeld.Coordinator.tables112_holds
        HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
        HardMathSupport.Solomon.Coordinator.tables112Types_holds
        HardMathSupport.Solomon.Coordinator.tables112More_holds kd2028S_holds kdSU3_holds
        hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1)
    (fun G _ _ m _ p hp => i1412UsedAt_of_kdLevelK hp.1.1 hp.1.2.1 (h p hp.1.1 hp.1.2.1)) hM hH

theorem ys02_of_m11_m13
    (h11 : KDSporRow .M 11) (h13 : KDSporRow .M 13) : YS02 :=
  ys02_of_kdLevelK
    (fun p hp hp2 => kdLevelK_of hp hp2
      (kdChevDown_of hp hp2 (kdCharP_of_lieQConstrainedInner hp
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.lieQConstrainedInner_odd hp hp2))
        (CFSG.HardMathSupport.Dickson.DefCharOuter.Export.kdOutChev_holds hp hp2)
        (ambiguous_downLe hp hp2 u42_downLe))
      (kdLevelTwoK_of hp hp2 kdRankTwoDown_holds kdAltDown_holds
        (kdLevelFiniteK_all CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group h11 h13 p hp hp2))
      (kdLevelThreeK_of kdRankTwoDown_holds kdAltDown_holds
        (kdLevelFiniteK_all CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
          CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group h11 h13 3
          Nat.prime_three (by decide))))
    (fun p _ _ => listedMultiplierBound_of_tables
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement sporadicMultiplierTable_holds p)
    (hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds)

end Certs

end CFSG.LocalAnalysis.GLTheoremA
