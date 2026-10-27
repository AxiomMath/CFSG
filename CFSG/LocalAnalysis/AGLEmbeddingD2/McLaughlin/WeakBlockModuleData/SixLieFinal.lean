module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieSpNoSwap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieNoSwapNode
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieNoSwapU5

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.LocalAnalysis.RankThreeTheoremC

theorem kFactBlockSixLieNoSwap_proved (hG : GriessAllModelsStatement) : KFactBlockSixLieNoSwap := by
  intro G _ _ M S L hK hAsc hL h2 hsolv hF E hEel hE9 hEP h9
  obtain ⟨hY, hpar, hS⟩ := h2
  have hperfX : Group.IsPerfect ↥(barM M L) :=
    Subgroup.isPerfect_iff.mpr (barM_perfect hL.le hL.perfect)
  have hZ3 := three_coprime_center_of_isFiveList hG hperfX hF
  rcases isFiveList_cases hF with h | h | h | h | h
  · exact noSwap_of_psp hL hpar hsolv (by norm_num) (by norm_num) h hZ3 hE9 hEP
  · exact noSwap_of_psp hL hpar hsolv (by norm_num) (by norm_num) h hZ3 hE9 hEP
  · exact noSwap_of_pomegaMinus_four hL hpar hsolv h hZ3 hE9 hEP
  · exact noSwap_of_psu_four hL hpar hsolv h hZ3 hE9 hEP
  · exact noSwap_of_psu_five hL hpar hsolv h hZ3 hEel hE9 hEP h9

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
