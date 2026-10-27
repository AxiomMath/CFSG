module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10St
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316G2

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

theorem fzr_types :
    FzR10Types := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT _ htP
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  have hPf := fzl_pfacts hstr (P := fzP t x₁ x₂ rho) rfl htP
  by_cases hc : IsMulCommutative (fzP t x₁ x₂ rho)
  · have hcomm := isMulCommutative_iff_of_setLike.mp hc
    rcases fzl_abelian_dichotomy hcomm hPf.card_P hstr.rho_ord hPf.nrm_P_rho hPf.rho_fpf
      hstr.ZE hPf.EP hstr.card_E hstr.card_Z hstr.E_exp hstr.E_sq hstr.E_invol hstr.Z_sq
      hstr.rho_nrm_E hPf.P_sq hstr.E_equiv with h1 | ⟨h2, h3, h4⟩
    · exact Or.inr (Or.inl h1)
    · exact Or.inl ⟨hcomm, h2, h3, h4⟩
  · refine Or.inr (Or.inr ⟨hc, fzl_316_nonab hstr hPf ?_⟩)
    by_contra hall
    push Not at hall
    exact hc (isMulCommutative_iff_of_setLike.mpr hall)

end CFSG.OddStandard.SmallF3.FritzII
