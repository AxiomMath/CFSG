module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Stmt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Exc
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Abel
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Lin
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Uni
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L34
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Small
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Spor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporMcL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporLy
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Alt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Sp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714L3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714U34
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltMain
public import CFSG.GH74.GLS.LU.Local.A3Reduce2
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.Generic.BarSubnormal
public import CFSG.GH74.Generic.S1.DecompCore
public import CFSG.GH74.Generic.S1.KL3Red
public import CFSG.GH74.Generic.S1.TFrame
public import CFSG.GH74.Generic.S1.TLeafA
public import CFSG.GH74.Generic.S1.TLeafBar
public import CFSG.GH74.Generic.S45.LEvenBender
public import CFSG.GH74.Generic.S45.LSporRows
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModels
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import Certificates.Certificate10025

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.GH74.GLS.IVK
open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

theorem ivk714_leaves
    (hLy : LyOuterTrivialInput) : Ivk714Leaves where
  alt := ivk714_alt
  m11 := ivk714_m11
  m12 := ivk714_m12
  m22 := ivk714_m22
  m23 := ivk714_m23
  j1 := ivk714_j1
  j2 := ivk714_j2
  j3 := ivk714_j3
  mcl := ivk714_mcl
  ly := ivk714_ly hLy
  l2 := ivk714_l2
  l3 := ivk714_l3
  u3 := ivk714_u3
  sp4 := ivk714_sp4
  g2 := ivk714_g2
  d4 := ivk714_d4
  l4 := ivk714_l4
  u4 := ivk714_u4
  l5 := ivk714_l5
  u5 := ivk714_u5
  ree := ivk714_ree
  l28 := ivk714_l28
  l216 := ivk714_l216
  l34 := ivk714_l34
  u34 := ivk714_u34
  sz8 := ivk714_sz8

theorem ivk_7_14_g4_proved
    (hLy : LyOuterTrivialInput) : IVK_7_14_g4 :=
  ivk_7_14_g4_of_leaves (ivk714_leaves hLy)

end CFSG.GH74.GLS.IVK.Proofs2
