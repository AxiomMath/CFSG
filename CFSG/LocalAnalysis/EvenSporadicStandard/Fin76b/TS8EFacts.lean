module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2Rest6
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Root
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCentFinal
public import Certificates.Certificate24614
public import Certificates.Certificate24615
public import Certificates.Certificate24616
public import Certificates.Certificate24617
public import Certificates.Certificate24618
public import Certificates.Certificate24619

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Sporadic.Schreier (j3P j3PermEquiv)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}

theorem OuterE.exists_eLabelling_sporadic
    (h : OuterE G L z t T E) (hW : WFacts L t E)
    (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    (∃ eltE : ℕ → G, ELabelling E t J2.uMulJ2 J2.uIdxJ2 eltE) ∨
      ∃ eltE : ℕ → G, ELabelling E t J3.uMulJ3 J3.uIdxJ3 eltE := by
  have hRC : RootFactsClass ↥L :=
    rootFactsClass_of_sporadic J2.rootFactsClass_P J3.rootFactsClass_j3P hJ
  rcases hJ with hL | hL
  · obtain ⟨e⟩ := hL
    let φ : ↥ComponentClassification.J2Cover.Models.P ≃* ↥L :=
      ((MulEquiv.subgroupCongr ComponentClassification.J2Cover.Models.P_eq_autP).trans
        ComponentClassification.J2Cover.nativeEquivP.symm).trans e.symm
    exact Or.inl (h.exists_eLabelling hW hRC (ULabelClass.of_mulEquiv φ J2.uLabelClass_P))
  · obtain ⟨e⟩ := hL
    let φ : ↥j3P ≃* ↥L := j3PermEquiv.symm.trans e.symm
    exact Or.inr (h.exists_eLabelling hW hRC (ULabelClass.of_mulEquiv φ J3.uLabelClass_j3P))

theorem OuterE.eFacts69
    (h : OuterE G L z t T E) (hW : WFacts L t E) (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    EFacts69 E t := by
  rcases h.exists_eLabelling_sporadic hW hJ with ⟨eltE, hlab⟩ | ⟨eltE, hlab⟩
  · exact Certificates.certificate24614 hlab
  · exact Certificates.certificate24615 hlab

theorem OuterE.eFacts611
    (h : OuterE G L z t T E) (hW : WFacts L t E) (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    EFacts611 E t := by
  rcases h.exists_eLabelling_sporadic hW hJ with ⟨eltE, hlab⟩ | ⟨eltE, hlab⟩
  · exact Certificates.certificate24616 hlab
  · exact Certificates.certificate24617 hlab

theorem OuterE.eFacts613
    (h : OuterE G L z t T E) (hW : WFacts L t E) (hJ : IsSporadic L .J2 ∨ IsSporadic L .J3) :
    EFacts613 E t := by
  rcases h.exists_eLabelling_sporadic hW hJ with ⟨eltE, hlab⟩ | ⟨eltE, hlab⟩
  · exact Certificates.certificate24618 hlab
  · exact Certificates.certificate24619 hlab

end CFSG.EvenSporadicStandard.Fin76b
