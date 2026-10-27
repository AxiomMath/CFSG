module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem pRank_top_le_one_of_isCyclic_sylow {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) :
    Open.pRank p (⊤ : Subgroup K) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine SectionRank.pRank_le hp.one_lt fun A _ hA => ?_
  rw [pow_one]
  exact card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA

theorem pRank_mulAut_le_two_of_isCyclic_sylow {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hZ : Subgroup.center K = ⊥) (T : Sylow p K)
    (hT : IsCyclic (T : Subgroup K))
    (hOut : Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨E, -, hE, hcard⟩ := pRank_attained p hp (⊤ : Subgroup (MulAut K))
  have h := elementary_rank_le_kernel_rank_add_image_rank p hp
    (QuotientGroup.mk' (inner K)) hE _ hcard
  rw [QuotientGroup.ker_mk'] at h
  have h1 : Open.pRank p (inner K) ≤ 1 := by
    have e1 : inner K = (⊤ : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
      exact MonoidHom.range_eq_map _
    rw [e1, pRank_map_of_injective p hp _ (mulAut_conj_injective hZ)]
    exact pRank_top_le_one_of_isCyclic_sylow hp T hT
  have h2 : Open.pRank p (E.map (QuotientGroup.mk' (inner K))) ≤ 1 :=
    (pRank_mono p hp le_top).trans hOut
  omega

theorem kFactBetaRank2_of (hOut : KFactOutCyclic) (hAR : KFactSmallAutRank) :
    KFactBetaRank2 := by
  intro K _ _ hs hnab hcat p hp hp2 T _ hrk hcond
  by_cases hc : IsCyclic (T : Subgroup K)
  · exact pRank_mulAut_le_two_of_isCyclic_sylow hp
      (CFSG.AGLEmbedding.center_eq_bot_of_isSimpleGroup_of_nonabelian hs hnab) T hc
      (hOut K hs hnab hcat p hp hp2 T hc)
  · exact hAR K hs hnab hcat p hp hp2 T hc (hcond.resolve_left hc) hrk

end CFSG.LocalAnalysis.RankThreeTheoremC
