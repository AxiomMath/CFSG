module

public import CFSG.ClassicalInvolution.Q3.TL4WylE4
public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2WCent
public import CFSG.ClassicalInvolution.Q3.TL4WylE

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan le_pSpan AEIdent AEIdentOn ThmDHyp)

section Cit3


theorem secIdE2Frame_proved : SecIdE2Frame := by
  intro n _ hP Y _ _ hn R S t hd hc hO2 hnc B₁ hB₁ B₂ hB₂ hB₂K
  have hK := CoreAssembly.mem_conjClass_self (tightCore R)
  rcases SecIdE2.thmDConcl_of hP hn hd hc hO2 with
    h1 | ⟨W, hW1⟩ | ⟨E, hE⟩ | h64 | ⟨m, hm, ⟨I⟩⟩ | h29
  · exact absurd (h1 B₁ hB₁.1 _ hK) hB₁.2.1
  · exact ⟨fun B hB v hv => AlphaFr.E2W.mul_mem_center_of_not_dConnected hd hc hO2 hW1 hnc hB hv,
      Wyl.ncard_omegaNbr_of_wSet hd hc hO2 hW1 hnc hB₁ hB₂ hB₂K⟩
  · exact absurd (SecClq.dConnected_of_e8_edge hd hO2 hE hB₁) hnc
  · obtain ⟨I⟩ := h64
    exfalso
    refine Wyl.false_of_triangle_of_labels hd hc hO2 (by norm_num) le_rfl I.φ I.ker_le
      (fun L hL => ?_) hB₁ hB₂ hB₂K
    obtain ⟨α, -, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, b, hlab⟩
  · by_cases hm9 : 9 ≤ m
    · exact absurd (AlphaFr.E2A.dConnected_of_aeIdent hd hc hO2 hm9 I) hnc
    by_cases hm8 : m = 8
    · subst hm8
      refine ⟨fun B hB v hv =>
        AlphaFr.E2A.mul_mem_center_of_aeIdent hd hc hO2 hm le_rfl I hB hv, ?_⟩
      obtain ⟨α, hα, b, hl₀⟩ := I.label _ hK
      exact Wyl.ncard_omegaNbr_of_labels8 hd hc hO2 I.φ I.ker_le I.label hl₀
        (I.label_surj α hα (!b)) (fun h' x => I.label_surj αᶜ h' x)
    · exact (Wyl.false_of_triangle_of_labels hd hc hO2 hm (by omega) I.φ I.ker_le I.label hB₁
        hB₂ hB₂K).elim
  · obtain ⟨I⟩ := h29
    refine ⟨fun B hB v hv =>
      AlphaFr.E2A.mul_mem_center_of_aeIdentOn hd hc hO2 (by norm_num) le_rfl I hB hv, ?_⟩
    obtain ⟨α, hα𝒜, hα, b, hl₀⟩ := I.label _ hK
    refine Wyl.ncard_omegaNbr_of_labels8 hd hc hO2 I.φ I.ker_le (fun L hL => ?_) hl₀
      (I.label_surj α hα𝒜 hα (!b)) (fun h' x => I.label_surj αᶜ (AE.e29Sets_compl hα𝒜) h' x)
    obtain ⟨β, -, h, b', hlab⟩ := I.label L hL
    exact ⟨β, h, b', hlab⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
