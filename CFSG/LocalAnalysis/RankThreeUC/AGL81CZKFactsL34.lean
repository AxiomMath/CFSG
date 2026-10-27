module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Sylow
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenTwoOneHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsA6
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZKFactsAlt
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient
import CFSG.Models.PGLOrders

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

theorem kFactCardL34_holds : KFactCardL34 := by
  rintro d ⟨Q, hQ, hd⟩
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nonempty_mulEquiv_projSL_of_lie_A2_four d
      ⟨Q, hQ, hd⟩
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSL_three_four]

theorem kFactAutL34_holds : KFactAutL34 := by
  rintro d ⟨Q, hQ, hd⟩
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nonempty_mulEquiv_projSL_of_lie_A2_four d
      ⟨Q, hQ, hd⟩
  have e' : (TauCeti.CFSGIndex.lie d).Group ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 2) :=
    e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  rw [Nat.card_congr (MulAut.congr e').toEquiv,
    CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut
      CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two]
  norm_num

theorem kFactThreeRankL34_holds : KFactThreeRankL34 := by
  intro L _ _ _ hL
  by_contra h
  push Not at h
  have h1 : CFSG.pRank 3 (⊤ : Subgroup L) ≤ 1 := by omega
  obtain ⟨d, ⟨Q, hQ, hd⟩, ⟨e⟩⟩ := hL
  obtain ⟨e₂⟩ :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section14.nonempty_mulEquiv_projSL_of_lie_A2_four d
      ⟨Q, hQ, hd⟩
  have hLZ : CFSG.pRank 3 (L ⧸ Subgroup.center L) = 2 := by
    refine CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_of_mulEquiv
      CFSG.RankThree.PartTwo.KFacts.L34.card_galoisField_two_two ?_
    exact e.trans (e₂.trans
      (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)))
  have hL1 : CFSG.pRank 3 L ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h1
  have hquot : CFSG.pRank 3 (L ⧸ Subgroup.center L) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
      Nat.prime_three (by norm_num) hL1 (QuotientGroup.mk' (Subgroup.center L))
      (QuotientGroup.mk'_surjective _)
  omega

theorem zkFacts_of_normalComplement (h : KFactNormalComplement) : ZKFacts :=
  { autL34 := kFactAutL34_holds
    cardL34 := kFactCardL34_holds
    autA11 := kFactAutA11_holds
    autA6 := kFactAutA6_holds
    rankL34 := kFactThreeRankL34_holds
    rankA11 := kFactThreeRankA11_holds
    omegaNotCentral := kFactOmegaNotCentral_holds
    normalComplement := h }

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
