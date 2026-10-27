module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10St
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRB2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRB3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRCore

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

theorem fzr_noB :
    FzR10NoB := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hsyl htP hZ
  obtain ⟨e⟩ := hZ
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  have hPf := fzl_pfacts hstr (P := fzP t x₁ x₂ rho) rfl htP
  obtain ⟨hPc, X, hXP, hX, hX16⟩ := fzr_B_omega e
  obtain ⟨s, hs, hsX⟩ := fzr_B_cent hstr hPf hPc hXP hX hX16
  exact fzr_fusion_core hctx hT hsyl hstr hPf hPc hXP hX hX16 hs hsX

end CFSG.OddStandard.SmallF3.FritzII
