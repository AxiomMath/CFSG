module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10St
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Dat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Real
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10Num2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import Certificates.Certificate441790
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319ShapeG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Triple

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

theorem fzr_shape :
    FzR10Shape := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hsyl htP hφ
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  obtain ⟨hN, hFu⟩ := Certificates.certificate441790
  obtain ⟨φ₀⟩ := hφ
  obtain ⟨D⟩ := fzr_data_nonempty hstr (P := fzP t x₁ x₂ rho) rfl htP φ₀ hN
  have hx₁ : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  rcases hFu D.cT D.cS D.cL D.validTriple with h | h
  · exact D.shape_sp hx₁ hx₂ hctx.wreath.conj_x₁
      (h (D.φ ⟨x₁, D.pf.EP hx₁⟩) (D.validX hx₁ hx₂ rfl hctx.wreath.conj_x₁))
  · exact absurd ⟨fzrTh (fzrCNum D), fzr_rules (fzrCNum D) hctx hK hT hsyl⟩ h

end CFSG.OddStandard.SmallF3.FritzII
