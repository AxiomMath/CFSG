module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFrameH0Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three


theorem twE6InnerA2CaseTwo_of_frameH0 (hR : TwE6SylowMonoTwoAt) (hF : TwE6CaseIFrameH0) :
    TwE6InnerA2CaseTwo := by
  rintro K _ _ σ q hK hσ hq hq2 E₀ hE₀ hc hN ⟨h₀, hh₀, hh₀1, hh₀24⟩
  have hK3 : ringChar K ≠ 3 := by
    refine ringChar_ne_three_of_not_dvd fun h3 => ?_
    rw [hK] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  obtain ⟨Fr, hFr, v, hv, g0, hg0C, hg0, ⟨a, ha, haΦ⟩, hmono⟩ :=
    hR K σ q hK hσ hq hq2 E₀ hE₀.isPGroup h₀ hh₀ (fun x hx => hE₀.comm hx hh₀)
      (hE₀.2 h₀ hh₀) hh₀24
  exact hF K σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN h₀ hh₀ hh₀1 hh₀24 Fr hFr v hv g0 hg0C hg0 a ha
    haΦ hmono

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
