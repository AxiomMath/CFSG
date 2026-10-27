module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoBaumHolds

import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderG2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSL3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4Main

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem k517_4b_thompsonJ_A2B2G2 :
    K517_4b_thompsonJ_A2B2G2 := by
  intro X _ _ T T₁ T₂ hX hGood Ls hY _ d hd _ hrt ⟨e⟩ q hq _ hdvd
  rcases hd with ⟨Q, hA | hB | hG⟩
  · obtain ⟨hn, ⟨eLs⟩⟩ := nonempty_mulEquiv_sl3_of_gnYComponent_A2 hX hGood hY hrt hA e hq hdvd
    exact gnImg_thompsonJ_le_sup_centralizer_of_A2 hX hY.1 hn
      (GaloisField.card 2 Q.exponent (Nat.pos_iff_ne_zero.mp Q.exponent_pos)) eLs
  · have hQ : Q.p = 2 := by
      rw [hB] at hrt
      exact hrt
    exact gnImg_thompsonJ_le_sup_centralizer_of_B2_cert113 hX hY.1 d Q hB hQ ⟨e⟩
  · have hQ : Q.p = 2 := by
      rw [hG] at hrt
      exact hrt
    obtain ⟨hn, ⟨eLs⟩⟩ := exists_mulEquiv_cayleyGroup_of_gn_component_G2 hX hY.1 d Q hG hQ ⟨e⟩
    exact gnImg_thompsonJ_le_sup_centralizer_of_G2 hX hY.1 hn
      (GaloisField.card 2 Q.exponent (Nat.pos_iff_ne_zero.mp Q.exponent_pos)) eLs

end CFSG.LocalAnalysis.RankThreeUC.S15

end
