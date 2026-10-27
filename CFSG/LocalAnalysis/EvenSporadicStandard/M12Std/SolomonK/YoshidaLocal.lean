module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.SolomonK.Consumer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLocalProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma3

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.M12Std.Yosh

theorem SolomonA12HypGL.toHypK {K : Type} [Group K] (h : SolomonA12HypGL K) :
    SolomonK.SolomonA12HypK K where
  fusionSimple := h.fusionSimple
  sylowType := h.sylowType
  exists_E := by
    obtain ⟨E, h2, hcard, -, hnn, he⟩ := h.exists_E
    exact ⟨E, h2, hcard, hnn, he⟩


theorem SolomonK.yoshida74LocalK_holds : SolomonK.Yoshida74LocalK := by
  intro G _ _ hG t ht he
  obtain ⟨e₀⟩ := he
  rcases exists_centralSwap e₀ ht with ⟨d, hd⟩ | ⟨d, hd⟩
  · obtain ⟨c, hc2, hperf, hZ, hhyp⟩ :=
      yoshida74LocalOfSwapGL_holds G hG t ht e₀ 0 d (Or.inl rfl) hd
    exact ⟨c, hc2, hperf, hZ, hhyp.toHypK⟩
  · obtain ⟨c, hc2, hperf, hZ, hhyp⟩ :=
      yoshida74LocalOfSwapGL_holds G hG t ht e₀ 1 d (Or.inr rfl) hd
    exact ⟨c, hc2, hperf, hZ, hhyp.toHypK⟩

end CFSG.EvenSporadicStandard.M12Std
