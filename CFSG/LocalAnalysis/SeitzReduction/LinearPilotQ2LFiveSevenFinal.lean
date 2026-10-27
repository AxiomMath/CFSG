module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKGLS
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenU47
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenOmega
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSevenExc

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.LinearPilot

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

section GLS

theorem lFiveSevenRankFamilyInput_of_eleven
    (hPSp : LFiveSevenRankFamilyInput .PSp) (hOO : LFiveSevenRankFamilyInput .POmegaOdd)
    (hOP : LFiveSevenRankFamilyInput .POmegaPlus) (hOM : LFiveSevenRankFamilyInput .POmegaMinus)
    (hG2 : LFiveSevenRankFamilyInput .G2) (hF4 : LFiveSevenRankFamilyInput .F4)
    (hE6 : LFiveSevenRankFamilyInput .E6) (hE7 : LFiveSevenRankFamilyInput .E7)
    (hE8 : LFiveSevenRankFamilyInput .E8) (h2E6 : LFiveSevenRankFamilyInput .twistedE6)
    (h3D4 : LFiveSevenRankFamilyInput .trialityD4) : ∀ t, LFiveSevenRankFamilyInput t := by
  intro t
  cases t
  exacts [lFiveSevenRankFamilyInput_PSL_holds, lFiveSevenRankFamilyInput_PSU_holds, hPSp, hOO,
    hOP, hOM, hG2, hF4, hE6, hE7, hE8, h2E6, h3D4,
    lFiveSevenRankFamilyInput_of_twisted (Or.inl rfl),
    lFiveSevenRankFamilyInput_of_twisted (Or.inr (Or.inr (Or.inl rfl))),
    lFiveSevenRankFamilyInput_of_twisted (Or.inr (Or.inl rfl)),
    lFiveSevenRankFamilyInput_of_twisted (Or.inr (Or.inr (Or.inr rfl)))]

theorem lFiveSevenRankFamilyInput_of_remaining (hPSp : LFiveSevenPSp47Input)
    (hF4 : ∀ f, Odd f → RankOne.ExcTwoPartInput .F4 7 f 6)
    (hE7 : ∀ f, RankOne.E7InnerTwoPartInput 7 f 6)
    (h2E6 : ∀ f, RankOne.TwistedE6InnerTwoPartInput 7 f 6)
    (h3D4 : RankOne.TrialityInnerTwoPartInput 7 1 6) : ∀ t, LFiveSevenRankFamilyInput t :=
  lFiveSevenRankFamilyInput_of_eleven (lFiveSevenRankFamilyInput_PSp_of_PSp47 hPSp)
    lFiveSevenRankFamilyInput_orthogonal_holds.1 lFiveSevenRankFamilyInput_orthogonal_holds.2.1
    lFiveSevenRankFamilyInput_orthogonal_holds.2.2
    (lFiveSevenRankFamilyInput_of_list lFiveSevenListFamilyInput_G2)
    (lFiveSevenRankFamilyInput_of_list (lFiveSevenListFamilyInput_F4_of_odd hF4))
    (lFiveSevenRankFamilyInput_of_list lFiveSevenListFamilyInput_E6)
    (lFiveSevenRankFamilyInput_of_list (lFiveSevenListFamilyInput_E7_of_inner hE7))
    (lFiveSevenRankFamilyInput_of_list lFiveSevenListFamilyInput_E8)
    (lFiveSevenRankFamilyInput_of_list (lFiveSevenListFamilyInput_twistedE6_of_inner h2E6))
    (lFiveSevenRankFamilyInput_of_list (lFiveSevenListFamilyInput_trialityD4_of_seven h3D4))

theorem lFiveSmallKindRankInput_of_remaining (hPSp : LFiveSevenPSp47Input)
    (hF4 : ∀ f, Odd f → RankOne.ExcTwoPartInput .F4 7 f 6)
    (hE7 : ∀ f, RankOne.E7InnerTwoPartInput 7 f 6)
    (h2E6 : ∀ f, RankOne.TwistedE6InnerTwoPartInput 7 f 6)
    (h3D4 : RankOne.TrialityInnerTwoPartInput 7 1 6) : LFiveSmallKindRankInput :=
  lFiveSmallKindRankInput_of_sevenFamilies
    (lFiveSevenRankFamilyInput_of_remaining hPSp hF4 hE7 h2E6 h3D4)

end GLS

end CFSG.SeitzReduction.LinearPilot
