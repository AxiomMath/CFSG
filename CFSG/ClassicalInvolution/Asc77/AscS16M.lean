module

public import CFSG.ClassicalInvolution.Asc77.AscS16L
public import CFSG.ClassicalInvolution.Asc77.AscS22K
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S16

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Final

variable (p f : ℕ) [Fact p.Prime]

theorem hyp22FourthTwinAb_of_z2 (hR1 : Z2NoD8 p) : S22.Hyp22FourthTwinAb p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h heq
  by_contra hcon
  push Not at hcon
  have hnb : ¬ S22.Big Ω K := fun hb => by
    obtain ⟨t, ht, h1, h2, h3⟩ := hb.fourth K K' K₃
    exact h3 (hcon t ht h1 h2)
  have hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K := fun J hJ =>
    T7S22.dComp_subset_twinSet h (by rw [heq]; exact hJ)
  have hAall := S22.hAall_of_dstarComp h hsig
  have hv : V3Ab Ω K := ⟨hnb, hAall⟩
  have hNT : CFSG.ClassicalInvolution.G2D4Models.G2NonToralGenerate p :=
    CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all
  have hE : ThmEWithSylow p f := thmEWithSylow_of_nonToral f hNT
  refine false_of_abelianV hE (c22_2V p f hR1) h hv hsig ?_
  intro L L' L₃ x y w hd
  have hLV : L ∈ twinSet Ω K := ⟨hd.stand.mem, z, h.hz, hd.hz⟩
  have hv' : V3Ab Ω L := hv.of_twin h.hz hLV
  exact S22.cent_of_zstar hd (layer_zStar hR1 hd (hv'.hV3 hd) hv'.2)

end Final

end S16

end CFSG.ClassicalInvolution.Asc77
