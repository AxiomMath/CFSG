module


public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace SourceSetting

namespace TwoGroupNormalizerMaxLocal

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_rankThreeIsMaxTwoLocal_ge {N : Subgroup G} (hN : IsTwoLocal N) :
    ∃ H : Subgroup G, rankThreeIsMaxTwoLocal H ∧ N ≤ H := by
  classical
  obtain ⟨H, hNH, hH⟩ := Set.Finite.exists_le_maximal
    (s := {H : Subgroup G | IsTwoLocal H}) (Set.toFinite _) (a := N) hN
  refine ⟨H, ⟨hH.1, fun K hK hHK => ?_⟩, hNH⟩
  exact le_antisymm_iff.2 ⟨(hH.2 hK hHK) , hHK⟩ |>.symm ▸ rfl

theorem normalizer_le_of_maxTwoLocalsContaining_eq_singleton
    {W J M : Subgroup G} (hW : W ≠ ⊥) (hW2 : IsPGroup 2 W)
    (hJ : J ≤ normalizer (W : Set G))
    (h : maxTwoLocalsContaining J = {M}) :
    normalizer (W : Set G) ≤ M := by
  obtain ⟨H, hH, hNH⟩ := exists_rankThreeIsMaxTwoLocal_ge
    (N := normalizer (W : Set G)) ⟨W, hW, hW2, rfl⟩
  have : H ∈ maxTwoLocalsContaining J := ⟨hH, hJ.trans hNH⟩
  rw [h] at this
  exact (this ▸ hNH)

end TwoGroupNormalizerMaxLocal

end SourceSetting

end CFSG.LocalAnalysis.RankThreeUC
