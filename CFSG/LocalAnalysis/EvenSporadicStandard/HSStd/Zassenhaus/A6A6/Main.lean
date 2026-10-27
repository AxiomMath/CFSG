module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Decomp
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Covers
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Wreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Main

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std

theorem prop21A6A6Case_proved : M22Std.Prop21A6A6Case := by
  intro V _ hc hs hV G _ _ ρ hρ z _ _ hE
  obtain ⟨e⟩ := hE
  obtain ⟨d⟩ := nonempty_decomp hc hs hV ρ hρ e
  obtain ⟨c⟩ := nonempty_config hc hs hV ρ hρ e d
  have hN := c.fusionOddCore_eq_bot hc hs hV hρ
  obtain ⟨f⟩ := c.nonempty_sup_equiv
  exact ⟨⟨(MulEquiv.subgroupCongr (c.egaLayer_eq hN)).trans f⟩,
    c.exists_wreath hc hs hV hρ hN⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
