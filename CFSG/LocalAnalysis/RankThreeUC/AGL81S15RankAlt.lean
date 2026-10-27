module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
import CFSG.Milestones.ASVolI.I2Covers
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Center
import CFSG.Quasithin.H13.A7SectionRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.RankThree.PerfectCover

theorem lieOddRankAlt_holds : LieOddRankAlt := by
  intro K _ _ hq n hn ⟨e⟩ r hr hr2
  have hq' : CFSG.IsQuasisimple K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1).2 hq
  haveI : Group.IsPerfect K := hq'.1
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hZ : r ∣ Nat.card (Subgroup.center K)
  · obtain ⟨rfl, hn67⟩ := (CFSG.HardMathSupport.Timmesfeld.Tables.Alt.center_facts hn e hr hr2).2 hZ
    have hπ := centralQuotientMap_surjective e
    have hk := centralQuotientMap_ker e
    have h2 : CFSG.pRank 3 K = 2 :=
      CFSG.ASVolI.burnsideI2a_pRank_three_cover_alternating (by omega) (by omega)
        (centralQuotientMap e) hπ hk.le
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
    rw [h2]
    rcases hn67 with rfl | rfl <;> norm_num
  · have h1 := CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e
    have h3 := (CFSG.Quasithin.H13.A7.section_rank_alternating_odd_prime_rank).1 n r hr hr2
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15
