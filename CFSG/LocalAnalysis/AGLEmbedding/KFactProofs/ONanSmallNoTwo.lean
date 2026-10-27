module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamNoTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamNoTwoAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallM11Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallNoTwoJ4
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallSylowExp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroKFacts

public section

namespace CFSG.AGLEmbedding

open KFactProofs.SmallIdent KFactProofs.UPrimeExcL34

theorem kFactSmallNoTwo_of_smallIdent
    (h : KFactSmallIdent) : KFactSmallNoTwo := by
  intro K _ _ hs hnab hc p hp hp2 T hT hΓ hAut hFi S U hU hSU
  have hexp := kFactSmallSylowExp_of_smallIdent h K hs hnab hc p hp hp2 T hT hΓ hAut
  rcases isSmallStrongP_of_autRank h hs hnab hc hp hp2 T hT hΓ hAut with
    hK | hK | hK | ⟨rfl, hK | hK⟩ | ⟨rfl, hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact noTwo_of_isSmallLinTwo hp hp2 hK S U hU hSU
  · exact noTwo_of_isSmallUnitary hp hp2 hK S U hU hSU
  · exact noTwo_of_isAltTwoP hp hp2 hK S U hU hSU
  · refine eq_bot_of_le_normalizer_of_isLinThreeFour hK ?_ ?_ hSU
    · rw [sylowSq_of_isLinThreeFour hK S]
      norm_num
    · obtain ⟨k, hk⟩ := hU.exists_card_eq
      rw [hk]
      intro h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
  · exact (sporCore_m11 hK T).noTwo_sylow hp hp2 hΓ (by rw [sylowSq_of_isM11 hK T]) hexp S U hU hSU
  · exact (sporCore_of_isTitsGroup hs hnab hK T).noTwo_sylow hp hp2 hΓ
      (by rw [sylowSq_of_isTitsGroup hK T]) hexp S U hU hSU
  · exact (sporCore_of_isMcL hs hnab hK T).noTwo_sylow hp hp2 hΓ
      (by rw [(sylowCube_of_isMcL hs hK T).1]; exact pow_dvd_pow 5 (by norm_num)) hexp S U hU hSU
  · exact absurd ⟨rfl, hK⟩ hFi
  · exact noTwo_of_isJ4 hs hK S U hU hSU

end CFSG.AGLEmbedding
