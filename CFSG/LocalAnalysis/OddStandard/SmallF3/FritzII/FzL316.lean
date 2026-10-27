module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316Fin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

theorem fzl_316 :
    Fz316 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  obtain ⟨hab, hnab⟩ := fzl_316_of_str hstr (P := fzP t x₁ x₂ rho) rfl hT.le_N2
    hT.odd_relIndex hns
  refine ⟨fun hc => hab (isMulCommutative_iff_of_setLike.mp hc), fun hc => hnab ?_⟩
  intro hcomm
  exact hc (isMulCommutative_iff_of_setLike.mpr hcomm)

end CFSG.OddStandard.SmallF3.FritzII
