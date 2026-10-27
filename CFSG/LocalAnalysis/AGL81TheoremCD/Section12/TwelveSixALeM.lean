module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIDataExists
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMLatter
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMFormer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMThreeFalse

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.not_pLayerIn_le (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hIM : TwelveSixIMember) : ¬ pLayerIn p H ≤ M := by
  intro hA
  obtain ⟨D⟩ := hc.exists_iData hIM
  have hY := hc.starImg_I_le_cStarL D hA
  have hp := hc.p_eq_three_of_starImg_le_cStarL D hY
  exact hc.false_of_starImg_le_cStarL_of_three D hp
    (hc.n_eq_one_of_starImg_le_cStarL D hp hY) hY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
