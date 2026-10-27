module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenRankOneDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenThreeCfg
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySeven

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem agl81ElevenThreeDvdCfg_of (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    (h1033 : AGL81TenThreeThreeCfg G) (hN1 : TenThreeThree.AGL81ElevenThreeInspectionCfg G)
    (h93X : AGL81NineThreeXCfg G) (h1031 : AGL81TenThreeOneAt G) (h10C : AGL81TenOneCZero G)
    (h91 : AGL81TenNineOneCfg G) : AGL81ElevenThreeDvdCfg G := by
  intro hS p P M H Q K hd _hnc L hL hLn
  have hXM := h93X hS p P M H Q K hd
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨I₀, hI₀⟩ := h10C hS 3 P M H Q K hd L hL (h91 hS 3 P M H Q K hd L hL)
    exact (h1031 hS 3 P M H Q K hd L hL I₀ hI₀).trans
      (Subgroup.card_dvd_of_le (IsCZeroMember.oUpperTwo_le_jOne hI₀))
  · have hQS : Q ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hd.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
    obtain ⟨R, hSR, hR⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
      (hd.b3 _ (pCoreOf_isPGroup 2 H) (pCoreOf_le 2 H) hQS) (pCoreOf_isPGroup 2 H) hQS
    have hR1 : R ≠ ⊥ := fun h0 => pCoreOf_two_ne_bot hd.maxH.1 (le_bot_iff.mp (h0 ▸ hSR))
    exact hd.prime_dvd_card_jOne_of_ne_three hS hCGT hD2 h1033 hN1 hp3 hXM hL hLn hR hR1

end CFSG.LocalAnalysis.RankThreeTheoremC
