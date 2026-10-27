module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Bs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59Fr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59U

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzl59a :
    Fz59A := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hr4 hctx hK hT hns hsh hbd
  have hB := fz59_base_of_ctx fz59Even_holds hr4 hctx hK hT hns hsh hbd
  obtain ⟨s, b, hF⟩ := fz59_frame hB
  obtain ⟨Φ, hΦ, hker, hcard, σ, hσ, hg⟩ := fz59_classify hB hF
  obtain ⟨s', u, b', T₃, hout⟩ := fz59_u hB hF hΦ hker hcard hσ hg
  exact ⟨s', u, b', T₃, hout.toT3Set hr4 hctx hK hT hns⟩

end CFSG.OddStandard.SmallF3.FritzII
