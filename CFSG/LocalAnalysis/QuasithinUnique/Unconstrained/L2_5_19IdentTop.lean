module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentEven
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentU3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentM12
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentU33
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL34
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentM11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentL5
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieTits
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieRee
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieSp4Four
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieG2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieD4

public section

namespace CFSG.QuasithinUnique.Id2519

open Ident

structure IdentOpen : Prop where
  coverG24 : TabIdentFor @FamCoverG24
  j4 : TabIdentFor (@FamSporadic .J4)
  hs : TabIdentFor (@FamSporadic .HS)
  he : TabIdentFor (@FamSporadic .He)
  ru : TabIdentFor (@FamSporadic .Ru)

theorem identFamilies_of_open
    (h : IdentOpen) : IdentFamilies where
  l2Even := tabIdentFor_l2Even
  l3Two := tabIdentFor_l3Two
  l3Four := tabIdentFor_l3Four
  l3Even := tabIdentFor_l3Even
  u3Four := tabIdentFor_u3Four
  u3Even := tabIdentFor_u3Even
  sp4Four := tabIdentFor_sp4Four
  sp4Even := tabIdentFor_sp4Even
  g2Even := tabIdentFor_g2Even
  trialityEven := tabIdentFor_trialityEven
  twistedF4 := tabIdentFor_twistedF4
  suzuki := tabIdentFor_suzuki
  tits := tabIdentFor_tits
  l4Two := tabIdentFor_l4Two
  l5Two := tabIdentFor_l5Two
  a6Simple := tabIdentFor_a6Simple
  u33 := tabIdentFor_u33
  coverL34 := tabIdentFor_coverL34
  coverG24 := h.coverG24
  alt6 := tabIdentFor_alt6
  alt7 := tabIdentFor_alt7
  l33 := tabIdentFor_l33
  l2Odd := tabIdentFor_l2Odd
  m11 := tabIdentFor_m11
  m12 := Tab.tabIdentFor_m12
  m22 := MathNoLayer.tabIdentFor_m22
  m23 := MathNoLayer.tabIdentFor_m23
  m24 := MathNoLayer.tabIdentFor_m24
  j2 := Tab.tabIdentFor_j2
  j4 := h.j4
  hs := h.hs
  he := h.he
  ru := h.ru

theorem tabIdent_of_open
    (h : IdentOpen) : TabIdent :=
  tabIdent_of_families (identFamilies_of_open h)

end CFSG.QuasithinUnique.Id2519
