module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentTop
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentCoverG24
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentRu
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHSFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentSporHe
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInner

public section

namespace CFSG.QuasithinUnique.Id2519

open Ident

structure IdentOpen2 : Prop where
  j4 : TabIdentFor (@FamSporadic .J4)

theorem tabIdent_of_open2
    (h : IdentOpen2) : TabIdent :=
  tabIdent_of_open
    { coverG24 := tabIdentFor_coverG24
      j4 := h.j4
      hs := SporHS.tabIdentFor_hs
      he := SporHe.tabIdentFor_he_of HeInner.he_inner_noK
      ru := MathNoLayer.tabIdentFor_ru }

end CFSG.QuasithinUnique.Id2519
