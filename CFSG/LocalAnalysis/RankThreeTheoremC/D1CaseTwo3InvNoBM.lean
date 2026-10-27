module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallCaseTwoInv
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMSeitz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.SmallIdent

theorem kFactCaseTwoInvNoBM_of_smallIdentNoBM
    (h : KFactSmallIdentNoBM) : KFactCaseTwoInvNoBM := by
  intro K _ _ hs hnab hc hBM p hp35 T hT hΓ hrk A L _ hL f hf
  have hp : p.Prime := by rcases hp35 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  have hK : IsSmallStrongP p K := h K hs hnab hc hBM p hp hp2 T hT hΓ
    ((CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp ⊤).le.trans hrk)
  rcases hp35 with rfl | rfl
  · obtain ⟨g, hg⟩ := exists_orderOf_nine_of_isCaseTwoGroup_three hL
    exact false_of_surjective_orderOf_sq hp (pow_eq_one_of_isSmallStrongP hp hp2 hs hK T hT) A f hf
      g (by simpa using hg)
  · have h1 : Nat.card L ∣ Nat.card A := Subgroup.card_dvd_of_surjective (f := f) hf
    have h2 : Nat.card A ∣ Nat.card K := Subgroup.card_subgroup_dvd_card A
    exact not_dvd_forty_one_of_isSmallStrongP hs hK
      ((forty_one_dvd_card_of_isCaseTwoGroup_five hL).trans (h1.trans h2))

end CFSG.LocalAnalysis.RankThreeTheoremC
