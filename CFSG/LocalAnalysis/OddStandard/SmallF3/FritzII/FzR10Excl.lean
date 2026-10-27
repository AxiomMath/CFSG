module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10St
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XMain
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzr_excl :
    FzR10Excl := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hsyl htP
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  exact fzr_excl_abstract (fzl_str hctx hK hT hF h37) htP

end CFSG.OddStandard.SmallF3.FritzII
