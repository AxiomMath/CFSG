module

public import CFSG.ClassicalInvolution.Asc77.AscT7S2RD
public import CFSG.ClassicalInvolution.Asc77.AscT7RG


public section

namespace CFSG.ClassicalInvolution.Asc77

variable (p f : ℕ) [Fact p.Prime]


theorem c21_14_Y_disc_of_S4 (hC3 : C21_3 p f) (hS4 : T7S2R.Ih8S4Star p f) :
    C21_14_Y_disc p f := by
  intro G _ _ _ Ω K K' z u J t W h hdisc
  rcases h.zt_of_not_sectionConnected hS4 hdisc with htriv | htriv
  · refine ⟨h.rLayer_u_le_normalizer_alpha_of_trivial hC3 (c₀ := z) (Or.inl rfl) htriv,
      fun hα => Or.inl ?_⟩
    exact h.rLayer_u_le_sigmaGen_of_trivial hα (c₀ := z) (Or.inl rfl) htriv fun R hR hRz =>
      h.rSet_le_sigmaGen_of_le_centralizer hR hRz
  · refine ⟨h.rLayer_u_le_normalizer_alpha_of_trivial hC3 (c₀ := t * z) (Or.inr rfl) htriv,
      fun hα => Or.inr ?_⟩
    have hY := h.rLayer_u_le_centralizer_tz_of_trivial hC3 hα htriv
    refine iSup₂_le fun R hR => iSup_le fun hRc => ?_
    have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR (le_iSup_of_le hRc le_rfl)
    exact le_iSup₂_of_le R hR (le_iSup_of_le (hRY.trans hY) le_rfl)

end CFSG.ClassicalInvolution.Asc77
