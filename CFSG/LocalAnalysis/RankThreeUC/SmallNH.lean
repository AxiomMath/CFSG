module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_pCoreOf_le_of_le {T X H : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTX : T ≤ X) (hXH : X ≤ H)
    (hH : H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H) :
    X ⊓ centralizer (pCoreOf 2 X : Set G) ≤ pCoreOf 2 X := by
  have hHQ : H ≤ normalizer (pCoreOf 2 H : Set G) := localGroup_le_normalizer_pCoreOf 2 H
  have hQT : pCoreOf 2 H ≤ T := by
    have hsup := hT.isPGroup.to_sup_of_normal_right' (pCoreOf_isPGroup 2 H)
      (hTX.trans (hXH.trans hHQ))
    exact sup_eq_left.mp (hT.eq_of_le le_sup_left le_top hsup)
  have hQX : pCoreOf 2 H ≤ pCoreOf 2 X := by
    refine normal_pGroup_le_pCoreOf 2 _ X (hQT.trans hTX) ?_ (pCoreOf_isPGroup 2 H)
    exact (normal_subgroupOf_iff_le_normalizer (hQT.trans hTX)).mpr (hXH.trans hHQ)
  exact fun g hg => hQX (hH ⟨hXH hg.1, centralizer_le hQX hg.2⟩)

theorem mem_hSet_of_le {T M X H : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hH : H ∈ hSet T M) (hTX : T ≤ X) (hXH : X ≤ H) (hXM : ¬ X ≤ M) : X ∈ hSet T M :=
  ⟨hTX, hXM, inf_centralizer_pCoreOf_le_of_le hT hTX hXH hH.2.2⟩

end CFSG.LocalAnalysis.RankThreeUC
