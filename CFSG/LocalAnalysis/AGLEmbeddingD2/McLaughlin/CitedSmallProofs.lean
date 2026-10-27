module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.PermJordan
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.AtlasOrders
public import CFSG.ThirdParty.OddOrder.Isaacs.PermutationGroups.PCycleJordan

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem jordanPrimeCycle_proved : JordanPrimeCycle := by
  intro α _ _ K p hp hcard hprim ⟨σ, hσK, hσc, hσp⟩
  exact CFSG.FiveTransitive.OddOrder.Isaacs.Ch08.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem
    hprim hp (by rwa [Nat.card_eq_fintype_card]) hσc hσp hσK

theorem l2SevenRankOne_proved : L2SevenRankOne := by
  intro d _ hd
  have h168 := OrdinaryProofs.l32Atlas_proved _ ⟨d, hd, ⟨MulEquiv.refl _⟩⟩
  have := pRank_top_le_one_of_card_168 h168
  omega

end CFSG.AGLEmbeddingD2.McLaughlin
