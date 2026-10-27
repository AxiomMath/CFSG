module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarThompsonPSp43
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarThompsonA9

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open Subgroup

theorem kFactKbarThompsonNormalizer_holds : KFactKbarThompsonNormalizer := by
  intro Y _ _ hY P B V hP hB hNB hVB hV hV27 h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hPp, hPi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  let P' : Sylow 3 Y := hPp.toSylow (by rwa [relIndex_top_right] at hPi)
  rcases hY with hL | hA
  · obtain ⟨⟨eW⟩, hc, hm⟩ := KbarThompson.psp43_facts hL P'
    exact KbarThompson.eq_normalizer_thompsonSubgroup P' eW hc hm hB hNB hVB hV hV27 h4
  · obtain ⟨e⟩ := hA
    obtain ⟨⟨eW⟩, hc, hm⟩ := KbarThompson.alt9_facts e P'
    exact KbarThompson.eq_normalizer_thompsonSubgroup P' eW hc hm hB hNB hVB hV hV27 h4

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
