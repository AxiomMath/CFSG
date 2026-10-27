module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalTen
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalNine
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalEightGLS3
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmqFinal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSigFinal
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2FieldFinal
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FamilyMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2Final
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveXiOmega
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerMain

public section

namespace CFSG.SeitzReduction

section Base

section RankOne

theorem seitzRankOneExclusion_holds : SeitzRankOneExclusion :=
  seitzRankOneExclusion_of_final8_gls3
    (RankOne.u3C1OuterMuOneSwapInput_of_high'
      (u3C1OuterSwapHighInput_of_final10 RankOne.gmiCatSL2CoverInput_holds))

end RankOne

section FieldKind

section PSL

theorem linearTwoFiveSixInput_of_final11_gls3 (hT : LinearPilot.LFiveFieldTildeSplitInput) :
    LinearPilot.LinearTwoFiveSixInput :=
  linearTwoFiveSixInput_of_final8_gls3
    (linearTwoFieldKindAtInput_five_of_final9 gls3OddLieAutComponentsInput
      LinearPilot.lFiveFieldSylowNormalInput_holds (lFiveGraphMcBrideInput_of_final10 hT)
      (Or.inr (lFiveGraphXCentralInput_of_final10 LinearPilot.lFiveGraphLeviNormInput_holds)))
    LinearPilot.lFiveSOneSylowPartInput LinearPilot.linearTwoSwapLabelDualAtInput_five
    LinearPilot.linearTwoSwapLabelDualAtInput_six

theorem seitzExclusion_highPSL_of_final11_gls3 (hT : LinearPilot.LFiveFieldTildeSplitInput) :
    SeitzExclusion HighPSL :=
  seitzExclusion_highPSL_of_final5 gls3OddLieAutComponentsInput
    (linearTwoFiveSixInput_of_final11_gls3 hT)

theorem seitzHighRankExclusion_of_final11_gls3 (hT : LinearPilot.LFiveFieldTildeSplitInput) :
    SeitzHighRankExclusion :=
  seitzHighRankExclusion_of_families (seitzExclusion_highPSL_of_final11_gls3 hT)
    (UnitaryPilot.seitzExclusion_highPSU_of_gls3 gls3OddLieAutComponentsInput)
    (seitzExclusion_highPSp_of_final9 gls3OddLieAutComponentsInput
      SymplecticPilot.spTwoLagDerivedClosureAt_four_two)
    seitzExclusion_highPOmegaPlus_holds seitzExclusion_highPOmegaMinus_holds
    (seitzExclusion_highF4_of_final9 gls3OddLieAutComponentsInput)
    (E6Pilot.seitzExclusion_highE6_of_gls3 gls3OddLieAutComponentsInput)
    (E7Pilot.seitzExclusion_highE7_of_gls3 gls3OddLieAutComponentsInput)
    (seitzExclusion_highE8_of_gls3 gls3OddLieAutComponentsInput)
    (seitzExclusion_highTwistedE6_of_final6 gls3OddLieAutComponentsInput)

section Reduction

theorem seitz_reduction_of_split (hT : LinearPilot.LFiveFieldTildeSplitInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (L : Subgroup G) (hL : CFSG.Open.standardComponentIsStandard L)
    (hcore : ∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (htype : CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L))
    (hexc : ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L))
    (hZ : Subgroup.center L = ⊥) :
    CFSG.Blueprint.NativeSporadic.SporadicRep L ∨
      CFSG.Blueprint.Recognition.Exact.EvenBNRankTwoType L ∨
      (CFSG.Blueprint.LieModel L .PSp 3 2 1 ∨ CFSG.Blueprint.LieModel L .PSU 6 2 1 ∨
        CFSG.Blueprint.LieModel L .POmegaMinus 4 2 1 ∨
        CFSG.Blueprint.LieModel L .POmegaPlus 4 2 1) :=
  seitz_reduction_of_exclusions seitzRankOneExclusion_holds
    (seitzHighRankExclusion_of_final11_gls3 hT)
    G hnonab hK L hL hcore S hS htype hexc hZ

end Reduction

end PSL

end FieldKind

end Base

end CFSG.SeitzReduction
