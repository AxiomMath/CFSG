module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L101
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Red3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPFin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10C105
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L103
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L104
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L106F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L108
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Red1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Red2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Z105

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Omega5Inputs10 : Prop where
  h6p : AschOmega6Plus
  h6m : AschOmega6Minus
  h7 : AschOmega7
  h8p : AschOmega8Plus
  h8m : AschOmega8Minus
  h6z : AschOmega6MinusZ2
  s3 : Asc82Sec3Res10
  facts : Asc82Facts10
  corIII : Asc82CorIII
  schur : Asc82SchurOmega5

theorem asc82Pre11_of_inputs10 (i : Asc82Omega5Inputs10) : Asc82Pre11 := by
  have hf := i.facts
  have h3 := i.s3
  have hb := asc82Basic10_of h3.l36 i.schur
  have h101 := asc82Lemma101_of i.h6p i.h6m i.h7 i.h8p i.h8m i.h6z
  have h102 := asc82Lemma102_of h3.l33 h101
  have h103 := asc82Lemma103_of h102 hb hf.sylow5
  have hK0 := asc82Lemma10K0_of h3.l36 h102 hb hf.pockets5 hf.out5
  have h104 := asc82Lemma104_of h3.l36 hK0 hb hf.pockets5 hf.centZ5
  have h105S := asc82Step105S_of h3.l37 h103 hb
  have h105C := asc82Step105C_of h105S h102 hb hf.pockets5 hf.centZ5 hf.f1051
  have h105T := asc82Step105T_of h105C h3.l36 h102 hK0 hb hf.pockets5 hf.centZ5 hf.centK5
  have h105Z := asc82Step105Z_of h3.l36 hb hf.pockets5
  have h105 := asc82Lemma105_of h105S h105T h105Z i.corIII
  have h106 := asc82Lemma106_of h3.l36 h3.l37 h102 h103 h105 hK0 hb hf.pockets5 hf.centZ5 hf.centK5
  have h107a := asc82Lemma107a_of hb hf.b5
  have h107b := asc82Lemma107b_of h3.l36 hb hf.b5
  have h107c := asc82Lemma107c_of h106 hb hf.f107c
  have h108 := asc82Lemma108_of h106 hb hf.out5 hf.n7
  let r10a : Asc82Res10a :=
    ⟨h101, h102, h103, hK0, h104, h105, h106, h107a, h107b, h107c, h108⟩
  have hKL := asc82StepKL_of hf.ce16 h3 r10a hf hb
  have h109A := asc82Step109A_of (asc82Step109AOuter_of h3 r10a hf hb) h3 r10a hb
  have h109B := asc82Step109B_of hKL h3 r10a hf hf.factsB hb
  have h109W := asc82Step109W_of hf.pockets5 hf.centZ5 h109B hb
  have h109C := asc82Step109C_of h109W hKL h3 r10a hf hb
  have h109D := asc82Step109D_of hK0 hf hb
  have h109 := asc82Lemma109_of h109A h109C h109D i.corIII
  have h1010 := asc82Lemma1010_of h105 h108 hb hf
  have h1011 := asc82Lemma1011_of h3.l36 r10a h109 h1010 hb hf
  exact ⟨h3, ⟨r10a, h109, h1010, h1011⟩, hf, hb⟩

end CFSG.OddStandard.SmallF3.Omega
