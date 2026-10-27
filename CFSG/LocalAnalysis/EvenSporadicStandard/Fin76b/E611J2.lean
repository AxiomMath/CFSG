module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentFinal
public import Certificates.Certificate24616

public section

namespace CFSG.EvenSporadicStandard.Fin76b.J2

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem eFacts611_of_isSporadic {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T₀ E : Subgroup G}
    (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t) (hL : IsSporadic L .J2) :
    EFacts611 E t := by
  obtain ⟨eltE, hlab⟩ := eLabelling_of_isSporadic h hE hL
  exact Certificates.certificate24616 hlab

end CFSG.EvenSporadicStandard.Fin76b.J2
