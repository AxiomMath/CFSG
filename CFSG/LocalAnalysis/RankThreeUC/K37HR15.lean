module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRGlue
public import CFSG.LocalAnalysis.RankThreeUC.K37HRCo1
public import CFSG.LocalAnalysis.RankThreeUC.K37HRFi
public import CFSG.LocalAnalysis.RankThreeUC.K37HRM
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne.Census3 (sporadicsThm3)
open TauCeti

theorem k37Rest₁₅_holds
    : K37Rest₁₅ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨s, hs3, ⟨e⟩⟩ := hO
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hs.quasi.2.1
  refine k37R_false_of_four_le_localRank hs (Y := K) ?_
  cases s
  case Co1 =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv
    exact k37R_coverRankFour_Co1.four_le_localRank (e.trans b.symm)
  case Fi22 =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
    exact k37R_coverRankFour_Fi22.four_le_localRank (e.trans b.symm)
  case Fi23 =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
    exact k37R_coverRankFour_Fi23.four_le_localRank (e.trans b.symm)
  case Fi24Prime =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
    exact k37R_coverRankFour_Fi24Prime.four_le_localRank (e.trans b.symm)
  case B =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.B.nonempty_mulEquiv
    exact k37R_coverRankFour_B.four_le_localRank (e.trans b.symm)
  case M =>
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
    exact (k37R_coverRankFour_M (e.trans b.symm)).four_le_localRank (MulEquiv.refl _)
  all_goals exact (hs3 (by simp [sporadicsThm3])).elim

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
