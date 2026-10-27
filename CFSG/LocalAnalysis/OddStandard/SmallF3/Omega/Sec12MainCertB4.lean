module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12MainCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111B4Cert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11TypeX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11SingleX

public section

namespace CFSG.OddStandard.SmallF3.Omega

structure Asc82Omega5Open' : Prop where
  h6p : AschOmega6Plus
  h6m : AschOmega6Minus
  h7 : AschOmega7
  h8p : AschOmega8Plus
  h8m : AschOmega8Minus
  h6z : AschOmega6MinusZ2
  s3 : Asc82Sec3Res10
  corIII : Asc82CorIII
  schur : Asc82SchurOmega5
  kBigSD : Asc82Step1111KBigSD
  s8Dich : Asc82S8Dich
  l63 : Asc82Lemma63
  l65 : Asc82Lemma65
  z4out : Asc82StepZ4Out
  z2a5 : Asc82Z2A5K
  zExists : Asc82ZExists

theorem aschOmega5_of_cert'
    (i : Asc82Omega5Open') : AschOmega5 :=
  have hp : Asc82Pre11 := asc82Pre11_of_inputs10
    { h6p := i.h6p
      h6m := i.h6m
      h7 := i.h7
      h8p := i.h8p
      h8m := i.h8m
      h6z := i.h6z
      s3 := i.s3
      facts := asc82Facts10_of_cert
      corIII := i.corIII
      schur := i.schur }
  aschOmega5_of_cert
    { h6p := i.h6p
      h6m := i.h6m
      h7 := i.h7
      h8p := i.h8p
      h8m := i.h8m
      h6z := i.h6z
      s3 := i.s3
      corIII := i.corIII
      schur := i.schur
      type1110 := asc82Step1110Type_of hp
      single1110 := asc82Step1110Single_of hp (asc82Step1110Type_of hp)
      dihSd := asc82InputDihSd_of_certificates
      kBigSD := i.kBigSD
      s8Dich := i.s8Dich
      l63 := i.l63
      l65 := i.l65
      z4out := i.z4out
      z2a5 := i.z2a5
      zExists := i.zExists }

end CFSG.OddStandard.SmallF3.Omega
