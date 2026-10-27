module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporadicCarrierFinite
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.McL
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co3
public import CFSG.LocalAnalysis.SectionRank.Sporadic.Co2

public section

namespace CFSG.AGLEmbedding

open CFSG.Blueprint CFSG.Open

theorem three_le_pRank_J3_three :
    3 ≤ pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .J3)) := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.J3_elementary_three_rank_three
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc

theorem three_le_pRank_McL_three :
    3 ≤ pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .McL)) := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
  exact (by norm_num : 3 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)

theorem three_le_pRank_Co3_three :
    3 ≤ pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co3)) := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Co3_elementary_three_rank_four
  exact (by norm_num : 3 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)

theorem three_le_pRank_Co2_three :
    3 ≤ pRank 3 (⊤ : Subgroup (NativeSporadic.Carrier .Co2)) := by
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Co2_elementary_three_rank_four
  exact (by norm_num : 3 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)

end CFSG.AGLEmbedding
