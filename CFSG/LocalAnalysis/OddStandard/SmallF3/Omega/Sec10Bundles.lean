module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactAutK5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactOuterI4m
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109CInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11InputsQ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Facts10 : Prop where
  sylow5 : Asc82FactSylow5
  out5 : Asc82FactOut5
  b5 : Asc82FactB5
  pockets5 : Asc82FactPockets5
  n7 : Asc82FactN7
  f1051 : Asc82Fact1051
  f107c : Asc82Fact107c
  f218c : Asc82Fact218c
  f218d : Asc82Fact218d
  f218e : Asc82Fact218e
  f218f : Asc82Fact218f
  centK5 : Asc82FactCentK5
  centZ5 : Asc82FactCentZ5
  centB5 : Asc82FactCentB5
  autAb : Asc82FactAutAb
  autK5 : Asc82FactAutK5
  outerI4m : Asc82FactOuterI4m
  factsC : Asc82FactsC
  factsB : Asc82FactsB
  ce16 : Asc82FactCE16
  invB : Asc82FactInvB
  autQ : Asc82FactAutQ

structure Asc82Res10a : Prop where
  l101 : Asc82Lemma101
  l102 : Asc82Lemma102
  l103 : Asc82Lemma103
  lK0 : Asc82Lemma10K0
  l104 : Asc82Lemma104
  l105 : Asc82Lemma105
  l106 : Asc82Lemma106
  l107a : Asc82Lemma107a
  l107b : Asc82Lemma107b
  l107c : Asc82Lemma107c
  l108 : Asc82Lemma108

structure Asc82Res10 : Prop extends Asc82Res10a where
  l109 : Asc82Lemma109
  l1010 : Asc82Lemma1010
  l1011 : Asc82Lemma1011

structure Asc82Sec3Res10 : Prop where
  l33 : Asc82Lemma33
  l36 : Asc82Lemma36
  l37 : Asc82Lemma37

end CFSG.OddStandard.SmallF3.Omega
