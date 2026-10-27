module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL316H7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL35f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzP35
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Std
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Main
public import Certificates.Certificate441787
public import Certificates.Certificate441788

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Bg.TwoGroups

theorem fzl_410 :
    Fz410 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT hns hφ
  obtain ⟨f, hf, hker⟩ := fzl_35b G t L S x₁ x₂ lam rho tau hr4 hctx hK
  have hF : FzF t x₁ x₂ f := ⟨hf, hker⟩
  have h37 := fz37R_of_35b fzl_35b G t L S T₂ x₁ x₂ lam rho tau hr4 hctx hK hT
  have hstr := fzl_str hctx hK hT hF h37
  have hnc : ¬ FzCanon T₂ (ctxW t x₁ x₂) := fun hc =>
    hns (fzl_sylow_of_canon hT.le_N2 hstr.pgroup_T hT.odd_relIndex hc)
  have htP : t ∉ fzP t x₁ x₂ rho := fun ht =>
    hnc (fzl_canon_of_phiQ hstr (fzl_phiQ_eq_W hstr ht))
  have hpf := fzl_pfacts hstr (P := fzP t x₁ x₂ rho) rfl htP
  obtain ⟨φ₀⟩ := hφ
  obtain ⟨hN, hA, hB⟩ := Certificates.certificate441787
  obtain ⟨s, emb, hs, hemb⟩ := fzl410_emb hN hA hB hstr hpf htP φ₀
  have hM : Fz410Mod t tau lam rho s _ _ _ _ _ _ _ emb := ⟨hstr, hpf, htP, hs, hemb⟩
  have hfacts := hM.facts Certificates.certificate441788
  exact (⟨hctx, hK, hT, hns, rfl, rfl, rfl, rfl, rfl, hstr, hpf, htP, ⟨f, hF⟩, hs, hfacts⟩ :
    Fz410Set t L S T₂ x₁ x₂ lam rho tau s _ _ _ _ _ _).main

end CFSG.OddStandard.SmallF3.FritzII
