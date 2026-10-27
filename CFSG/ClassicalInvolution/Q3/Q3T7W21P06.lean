module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21N09
public import CFSG.ClassicalInvolution.Q3.Q3T7W21P05

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7W21

open CFSG.ClassicalInvolution.Q3.Q3T7 CFSG.ClassicalInvolution.Q3.Q3T8.Asc77


theorem c21_14_Y_conn_W_of_spinGen3 (hG : Q3SPN3.SpinGen3) (hC3 : Q3T8.Asc77.C21_3) :
    C21_14_Y_conn_W := by
  intro G _ _ _ Ω K K' z u J t W h _ hα hne _
  by_cases hD : SectionDConnected Ω u
  · exact Or.inl (h.exactLayer_u_le_sigmaGen_of_dconn hα hD)
  rcases h.zt_or_le_sigmaNorm_of_not_sectionDConnected hG hα hD with htriv | htriv | hN
  · exact Or.inl (h.exactLayer_u_le_sigmaGen_of_le_centralizer_z
      (h.exactLayer_u_le_centralizer_of_trivial hC3 hα (c₀ := z) (Or.inl rfl) htriv))
  · exact Or.inr (h.exactLayer_u_le_centralizer_of_trivial hC3 hα (c₀ := t * z) (Or.inr rfl) htriv)
  · obtain ⟨r, hrY, hrS⟩ := h.exists_r_not_sigmaNorm hne
    exact absurd (hN hrY) hrS

theorem c21_2Three_of_spinGen3 (hE : Q3T7E.ThmEWithSylow3) (hHt : TwinFrameHyp51t)
    (hHu : TwinFrameHyp51u) (hG : Q3SPN3.SpinGen3) : C21_2Three :=
  c21_2Three_of_conn_W hE hHt hHu
    (c21_14_Y_conn_W_of_spinGen3 hG
      (c21_3_of (twinFrameHyp51_of_cases twinFrameHyp51z_proved hHt hHu)))

end CFSG.ClassicalInvolution.Q3.Q3T7W21
