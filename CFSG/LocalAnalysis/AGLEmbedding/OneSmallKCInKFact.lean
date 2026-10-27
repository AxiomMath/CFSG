module

public import CFSG.LocalAnalysis.AGLEmbedding.KGenTwoModAbFix
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux
import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

namespace ReducedNongeneration

variable {X : Type} [Group X] [Finite X] {R : Sylow 3 X} {X₀ : Subgroup X}

theorem false_of_smallCoverThree_of_mem (h : ReducedNongeneration 3 X R X₀)
    (hR3 : Open.pRank 3 (R : Subgroup X) ≤ 3) (hX : CatalogSimpleSections X) {z : X}
    (hz : z ∈ Subgroup.center X) (hzp : orderOf z = 3) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hKn : K.Normal) (hzK : z ∈ K) (hKF : KFactCoverThreeFix) :
    False := by
  have hp := h.prime
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  have hnc := h.not_isCyclic_inf_of_mem hz hzp hK hzK
  obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hrank : Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    rw [← (SectionRank.pRank_sylow T).1,
      ← pRank_map_of_injective 3 hp K.subtype K.subtype_injective, hT]
    exact (pRank_mono 3 hp inf_le_left).trans hR3
  rcases hKF K hK.2.2 (hX.isCatalogGroup_center_quotient hK) (center_ne_bot_of_mem hp hz hzp hzK)
      (isPGroup_center_of_isComponentOf hp h.core_eq_bot hK) (h.isCyclic_center hK hKn) hrank T
      with ⟨hgen, hZ3, hout⟩ | ⟨hc, h3⟩
  · exact h.false_of_kOutNormalSylow (h.le_of_kGenTwoModAbFix hz hzp hK hKn hzK hZ3 hgen)
      (h.centralizer_le_of_not_isCyclic hKn hnc) hout
  · exact h.false_of_three_le_pRank_of_le hKn (le_of_weakCore_eq_top h T hT hc) h3

end ReducedNongeneration

end CFSG.AGLEmbedding
