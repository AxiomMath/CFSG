module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Main
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactsOfCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12FactSplitModel
public import Certificates.Kernel.SporSch.Th.Key2311
public import Certificates.Kernel.SporSch.Th.Orb2315
public import Certificates.Kernel.SporSch.Th.Plane2320
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45c
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Shapes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.OddStandard.SmallF3.Omega

structure Asc82Omega5Open : Prop where
  h6p : AschOmega6Plus
  h6m : AschOmega6Minus
  h7 : AschOmega7
  h8p : AschOmega8Plus
  h8m : AschOmega8Minus
  h6z : AschOmega6MinusZ2
  s3 : Asc82Sec3Res10
  corIII : Asc82CorIII
  schur : Asc82SchurOmega5
  type1110 : Asc82Step1110Type
  single1110 : Asc82Step1110Single
  dihSd : Asc82InputDihSd
  kBigSD : Asc82Step1111KBigSD
  s8Dich : Asc82S8Dich
  l63 : Asc82Lemma63
  l65 : Asc82Lemma65
  z4out : Asc82StepZ4Out
  z2a5 : Asc82Z2A5K
  zExists : Asc82ZExists

theorem aschOmega5_of_cert
    (i : Asc82Omega5Open) : AschOmega5 :=
  aschOmega5_of_inputs
    { h6p := i.h6p
      h6m := i.h6m
      h7 := i.h7
      h8p := i.h8p
      h8m := i.h8m
      h6z := i.h6z
      s3 := i.s3
      facts := asc82Facts10_of_cert
      corIII := i.corIII
      schur := i.schur
      type1110 := i.type1110
      single1110 := i.single1110
      dihSd := i.dihSd
      kBigSD := i.kBigSD
      s8Dich := i.s8Dich
      l63 := i.l63
      l65 := i.l65
      z4out := i.z4out
      z2a5 := i.z2a5
      split5 := asc82FactSplit5_of_cert
      zExists := i.zExists }

end CFSG.OddStandard.SmallF3.Omega
