module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EFacts
public import Certificates.Certificate27802

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem OuterE.eFacts614
    (h : OuterE G L z t T E) (hW : WFacts L t E) (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    EFacts614 E t := by
  rcases h.exists_eLabelling_sporadic hW hJ with ⟨eltE, hlab⟩ | ⟨eltE, hlab⟩
  · exact Certificates.certificate27802.1 hlab
  · exact Certificates.certificate27802.2 hlab

end CFSG.EvenSporadicStandard.Fin76b
