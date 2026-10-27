module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Core
public import Certificates.Certificate441782

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

theorem fzl_319 :
    Fz319 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hφ
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  obtain ⟨hN, hC⟩ := Certificates.certificate441782
  obtain ⟨φ₀⟩ := hφ
  exact fzl_319_of_str hstr (P := fzP t x₁ x₂ rho) rfl hT.le_N2 hT.odd_relIndex hns φ₀ hN hC
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) rfl
    hctx.wreath.conj_x₁

end CFSG.OddStandard.SmallF3.FritzII
