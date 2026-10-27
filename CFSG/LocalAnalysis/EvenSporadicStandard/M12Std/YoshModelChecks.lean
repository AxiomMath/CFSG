module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFusion

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

structure ModelChecks : Prop where
  fusion : ∀ α k, α < 2 → k < 2 → FusionData α k
  ue : ∀ α k, α < 2 → k < 2 → ueCheck α k = true
  es : ∀ α k, α < 2 → k < 2 → esCheck α k = true
  l6 : ∀ k, k < 2 → l6Check 0 k = true
  l7 : ∀ k, k < 2 → l7Check 1 k = true
  l8 : ∀ k, k < 2 → l8Check 1 k = true
  sylowHom : ∀ k, k < 2 →
    sylowHomCheck (wgens 1 k sWords) (nwT 1 k cWord) (sylowHomData k) = true

end CFSG.EvenSporadicStandard.M12Std.Yosh
