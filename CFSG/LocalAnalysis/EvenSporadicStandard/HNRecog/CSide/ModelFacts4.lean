module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts3a

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

theorem cSideOmega_sigma0 (h : cSideModelProp) : CSideOmega q0 sigma0 := by
  have hK6c : cSideK6c := h.2.2.2.2.2.2
  have hcomm : ∀ g : A5 × A5, omega0 * sigma0 g = sigma0 g * omega0 := by
    intro g
    refine LinearEquiv.ext fun M => ?_
    have hg := omegaFun_actFun (iota g.1, iota g.2) M
    rw [LinearEquiv.mul_apply, sigma0_apply, LinearEquiv.mul_apply, sigma0_apply]
    exact hg
  refine ⟨omega0, hcomm, ?_, ?_⟩
  · intro v
    exact hK6c.1 v
  · intro b hb v
    obtain ⟨m, hm⟩ := exists_eq_sigma0_mul_b0 h hb
    have hca : ∀ x : V0, sigma0 m (omega0 x) = omega0 (sigma0 m x) := by
      intro x
      have hg := congrArg (fun e : V0 ≃ₗ[ZMod 2] V0 => e x) (hcomm m)
      simpa only [LinearEquiv.mul_apply] using hg.symm
    rw [hm]
    simp only [LinearEquiv.mul_apply]
    rw [show b0 (omega0 v) = omega0 (omega0 (b0 v)) from hK6c.2 v]
    rw [hca (omega0 (b0 v)), hca (b0 v)]

end CFSG.EvenSporadicStandard.HNRecog.CSide
