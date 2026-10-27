module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Main10
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Fusion2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3A6A6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Sp44

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem fin77aOuterResidue₃_holds :
    Fin77aOuterResidue₃ :=
  ⟨fin77aOuterFusion_of_facts autSylowEngine6_m22 autSylowCensus_m22 autSylowE32_m22, fin77aOuterResidue₃_a6a6, fin77aOuterResidue₃_sp44⟩

theorem m22_not_standard_of_prop21
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) (hP : Fin77aProp21K)
    (h25 : Finkelstein77.Asc76Lemma25) (hSplit : HaradaSolomon08M22Split) (h : StdHyp G L) :
    ¬ IsSporadic (L ⧸ center L) .M22 :=
  m22_not_standard_of_residue₃ hSol hP fin77aOuterResidue₃_holds h25 hSplit h

end CFSG.EvenSporadicStandard.M22Std
