module



public import CFSG.LocalAnalysis.RankThreeUC.NormalModules
import all CFSG.LocalAnalysis.RankThreeUC.NormalModules
public import CFSG.LocalAnalysis.RankThreeUC.Section12.NonTIUniqueRankTwo

public section


namespace CFSG.LocalAnalysis.RankThreeUC.Section12.NonRankOneNormalizerOddRank


variable {G : Type} [Group G] [Finite G]


theorem pRank_normalizerCentralizerIn_le_one {M T V₀ : Subgroup G} (hc : Context G M T)
    (hV : V₀ ∈ normalElemAbelian2 M) {p : ℕ} (hp : p ∈ SourceSetting.sigmaOf G M)
    (hnot : V₀ ∉ normalElemAbelian2One M T) :
    CFSG.Assembly.pRank p (normalizerCentralizerIn M T V₀) ≤ 1 := by
  by_contra h
  push Not at h
  refine hnot ⟨hV, fun N hN hle => ?_⟩
  exact NonTIUniqueRankTwo.unique_of_rank_two hc hp (X := normalizerCentralizerIn M T V₀)
    inf_le_left h N hN hle


end CFSG.LocalAnalysis.RankThreeUC.Section12.NonRankOneNormalizerOddRank
