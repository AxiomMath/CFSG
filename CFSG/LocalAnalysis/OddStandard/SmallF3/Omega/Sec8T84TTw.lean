module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TTwMain

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84FactTwist_holds : Sec8T84FactTwist := by
  intro G _ _ L P B₁ B₂ hL hP hne hB₁ hB₂ _ γ hγP hγγ hout
  obtain ⟨V, _, _, _, Q, hQ, e, x, hdim, hsgn, hs, hxx, hxG⟩ := hout
  obtain ⟨e', fr, x', hB₁fr, hPfr, hs', hxx', hxG'⟩ :=
    sec8t84tw_adapt hL hP hB₁ hdim hsgn e hs hxx hxG
  have hφ : OddCentralCover (ff6mPhi e') := ff6m_phi_cover e' (ff6m_odd_center hL)
  obtain ⟨r, hrP, hrr, ⟨y, hy, hyy, hyG⟩, hcard, hel⟩ :=
    sec8t84tw_main hdim hsgn hφ hP.1 hP.2.1 hB₁ hB₂ hne hB₁fr hPfr hγP hγγ hs' hxx' hxG'
  exact ⟨r, hrP, hrr, ⟨V, _, _, _, Q, hQ, e', y, hdim, hsgn, hy, hyy, hyG⟩, hcard, hel⟩

end CFSG.OddStandard.SmallF3.Omega
