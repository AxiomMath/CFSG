module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614R3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTwoLin
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614KTwoUni
import CFSG.RankThree.PartTwo.Census.Suzuki
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open P614KTwo

theorem kFactTwoInvolutionsThree_of_rankOne (h : KFactChevTwoRankOneThree) :
    KFactTwoInvolutionsThree := by
  intro K _ _ hs hna hc hr R hR hRc hRI
  exfalso
  refine hRc (OutTwoCyclic.isCyclic ?_ hR hRI)
  by_cases hB : fusionIsBenderGroup K
  · rcases hB with ⟨f, -, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact OutTwoCyclic.of_mulEquiv e (outTwoCyclic_of_isCyclic_outer (isCyclic_outer_psl2 _))
    · exact OutTwoCyclic.of_mulEquiv e (outTwoCyclic_psu3 hf)
    · exfalso
      have h3 : 3 ∣ Nat.card K := prime_dvd_card_of_pRank_pos 3 ⊤ (by rw [hr]; norm_num)
      rw [Nat.card_congr
        (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv] at h3
      exact CFSG.RankThree.PartTwo.Census.not_three_dvd_card_suzukiMatrixGroup (by omega) h3
  · obtain ⟨n, hn, ⟨e⟩⟩ := h K hs hna hc hr hB
    exact OutTwoCyclic.of_mulEquiv
      (e.trans (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3
          (GaloisField 2 n))).symm)
      (outTwoCyclic_of_isCyclic_outer
        (isCyclic_outer_projectiveSL_three (GaloisField.card 2 n hn.pos.ne') hn))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
