module

public import CFSG.ClassicalInvolution.Asc77.AscS22I
public import CFSG.ClassicalInvolution.Asc77.AscT7V7
import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive
public import CFSG.ClassicalInvolution.Asc77.AscS22F

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace S22

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Final

variable (p f : ℕ) [Fact p.Prime]

theorem hyp22SigmaNeX4_proved : T7V.Hyp22SigmaNeX4 p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ h K₄ hK₄ h1 h2 h3 heq
  have hb : Big Ω K := Big.of_four h hK₄ h1 h2 h3
  have hsig : ∀ J ∈ dstarComp Ω K, J ∈ twinSet Ω K := fun J hJ =>
    T7S22.dComp_subset_twinSet h (by rw [heq]; exact hJ)
  have hAall := hAall_of_dstarComp h hsig
  have hNT : CFSG.ClassicalInvolution.G2D4Models.G2NonToralGenerate p :=
    CFSG.ClassicalInvolution.G2D4Models.g2NonToralGenerate_all
  have hE : ThmEWithSylow p f := thmEWithSylow_of_nonToral f hNT
  refine false_of_abelian hE (c22_2S p f) h hb hsig ?_
  intro L L' L₃ x y w hd
  have hLV : L ∈ twinSet Ω K := ⟨hd.stand.mem, z, h.hz, hd.hz⟩
  obtain ⟨L₄, hL₄, e1, e2, e3⟩ := (hb.of_twin h.hz hLV).fourth L L' L₃
  exact cent_of_zstar hd (layer_zStar hd hL₄ e1 e2 e3 hAall)

theorem hyp22SettingWyl_of_fourthTwin (h3 : Hyp22FourthTwin p f) : T7V.Hyp22SettingWyl p f :=
  T7V.hyp22SettingWyl_of_sigmaNe (T7V.hyp22SigmaNe_of_split h3 (hyp22SigmaNeX4_proved p f))

end Final

end S22

end CFSG.ClassicalInvolution.Asc77
