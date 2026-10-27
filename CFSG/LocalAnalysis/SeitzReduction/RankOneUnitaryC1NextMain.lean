module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextHKS
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextUntwist
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextCentral

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

section Certificates

theorem u3C1NextInput : U3C1NextInput := by
  intro G _ _ L f t T d V U U₁ k h _ hsc hμV hlam hν hU
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := h.coords
  have H : U3C1Next G L f t T d V U U₁ k K v μ :=
    { stage := h, card_K := hK, coords := hc, gen := hμ, mu := hμV, lam := hlam, nu := hν }
  obtain ⟨E, hE⟩ := H.exists_regData hU
  obtain ⟨U₁', hL⟩ := (H.nextUData_u3C1U hE hsc).exists_levelData
  exact ⟨_, U₁', hL⟩

end Certificates

end CFSG.SeitzReduction.RankOne
