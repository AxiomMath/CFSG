module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.Main6
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutXbarCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutResidue3

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem m22_not_standard_of_residue₃
    (hSol : CFSG.EvenSporadicStandard.Fin76b.SolomonZ2A6) (hP : Fin77aProp21K)
    (hRes : Fin77aOuterResidue₃) (h25 : Finkelstein77.Asc76Lemma25)
    (hSplit : HaradaSolomon08M22Split) (h : StdHyp G L) :
    ¬ IsSporadic (L ⧸ center L) .M22 :=
  m22_not_standard_of_split hSol fin77aOuterXbar (fin77aOuterRest₄_of_residue₃ hP hRes) h25 hSplit h

end CFSG.EvenSporadicStandard.M22Std
