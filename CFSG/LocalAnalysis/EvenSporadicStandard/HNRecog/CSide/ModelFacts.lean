module

public import Certificates.Certificate442021
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts3b
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.TransportA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.TransportB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.TransportC
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ML1.MT0b

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

theorem cSideModel_sigma0 : CSideModel q0 sigma0 := by
  have h : cSideModelProp := cSideModelProp_of_ok Certificates.certificate442021
  exact ⟨cSideFixedZero_sigma0 h, cSideThreeBoth_sigma0 h, cSideInvol_sigma0 h,
    cSideOrbits_sigma0 h, cSideFiveBoth_sigma0 h, cSideOmega_sigma0 h⟩

theorem cSideModel_of_stdHyp {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (q : QuadraticForm (ZMod 2) V)
    (hnd : q.polarBilin.Nondegenerate) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (hS : Swap.StdHyp σ) (hq : ∀ g u, q (σ g u) = q u) : CSideModel q σ := by
  obtain ⟨a, ψ, hqa, hψ⟩ := ML1.mt0b q0 q q0_nondegenerate hnd sigma0 σ stdHyp_sigma0 hS
    q0_sigma0 hq
  have h := cSideModel_sigma0
  exact ⟨cSideFixedZero_transport a ψ hψ h.fixed_zero,
    cSideThreeBoth_transport a ψ hψ hqa h.three_both, cSideInvol_transport a ψ hψ h.invol,
    cSideOrbits_transport a ψ hψ hqa h.orbits, cSideFiveBoth_transport a ψ hψ hqa h.five_both,
    cSideOmega_transport a ψ hψ hqa h.omega⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
