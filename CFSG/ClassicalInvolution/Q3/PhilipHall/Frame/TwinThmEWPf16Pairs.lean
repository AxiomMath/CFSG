module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf15Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW

section Bridge

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE in
theorem wFreeToAll_proved : WFreeToAll := by
  intro G _ _ Ω K S R W H hst hE
  have hΩ := hst.hyp
  have hKW : K ⊓ W ∈ USet Ω :=
    inf_W_mem_USet' hΩ hst.hW.1 hst.hW.2.1 hst.mem hst.hR.1 hst.hR.2.1 hst.hR.2.2
  refine ⟨hE.trans, ?_⟩
  intro M hM hMW J hJ R₁ R₂ hR₁ hR₁M _ hR₂ hR₂J _ hcomm a haR _ ha1 ha2
  have hMsg : M ∈ dstarComp Ω K := mem_dstarComp_of_inf_W hΩ hst.hW.1 hst.mem hM hKW hMW
  obtain ⟨h, hhH, rfl⟩ := hE.trans M hMsg
  have hcsp : CentralizersSylowPairs Ω (conjSub h K) H := by
    have := hE.cent.conj hΩ.conjInvariant h
    rwa [conjSub_eq_self_of_mem hhH] at this
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hM
  exact hcsp _ ⟨hM, z, hz, hz⟩ J hJ R₁ R₂ hR₁ hR₁M hR₂ hR₂J hcomm a haR ha1 ha2

end Bridge

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
