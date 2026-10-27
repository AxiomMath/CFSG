module

public import CFSG.GH74.Generic.BProg.B2.PuL4GraphUni

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial Subgroup

section Certified


theorem puL4m_of_gen4_proved {N : Type} [Group N] [Finite N] (H : Subgroup N) (t : N)
    (L : Subgroup N) (hs : ShapeInCent H t L) (h4 : SectionalTwoRankLE N 4) (hJ : PuL4 ↥H) :
    PuL4m ↥H :=
  puL4m_of_gen4_uni outGraphUni_proved H t L hs h4 hJ

end Certified

end CFSG.GH74.Generic.BProg.B2
