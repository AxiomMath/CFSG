module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final13
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888LSQ
public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

structure Asc82Sec5Inputs15 : Prop where
  tab : Asc82Tab5
  tab56 : Asc82Tab56
  factB : Asc82Sec5FactB5
  fact512K : Asc82Fact512K
  l58b : Asc82Lemma58b
  l58d : Asc82Lemma58d
  f510 : Asc82Fact510
  fact512H : Asc82Fact512H
  facts6 : Asc82Sec5Facts6
  f513 : Asc82Fact513Comm
  m1 : Asc82FactRhoStar
  f7 : Asc82Fact512M8
  l511csl : Asc82Lemma511CSL
  cent6 : Asc82FactOm6CentD
  nrank6 : Asc82FactOm6NRank
  par5 : Asc82FactOm6Par
  corIIIq : Asc82CorIIIq

theorem asc82Sec5Inputs13_of_inputs15 (h3 : Asc82Sec3Results) (h7 : AschOmega7)
    (i : Asc82Sec5Inputs15) : Asc82Sec5Inputs13 :=
  have h51 : Asc82Lemma51 := asc82Lemma51_of h7 h3.l38 h3.l311
  have h52a : Asc82Lemma52a := asc82Lemma52a_of h3.l33 h51
  have h514 : Asc82Lemma514 := asc82Lemma514_of h3.l37 (asc82Lemma513_of h3.l36 h3.l37 i.f513)
  { tab := i.tab
    tab56 := i.tab56
    factB := i.factB
    fact512K := i.fact512K
    l58b := i.l58b
    l58d := i.l58d
    f510 := i.f510
    fact512H := i.fact512H
    facts6 := i.facts6
    f513 := i.f513
    l515S := asc82Lemma515Setting_of_m1 h3.l36 h3.l37 h514 h52a i.m1 h3.l38 h3.l311 h7
      CFSG.GH74.GLS.Stage2.Final.modelOneClass
    f7 := i.f7
    l511csl := i.l511csl
    cent6 := i.cent6
    nrank6 := i.nrank6
    par5 := i.par5
    corIIIq := i.corIIIq }

theorem aschOmega6MinusZ2_of_inputs15
    (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (hGold : GoldStmt)
    (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) (i : Asc82Sec5Inputs15) :
    AschOmega6MinusZ2 :=
  aschOmega6MinusZ2_of_inputs13 h3 h34a h7 hZ hO hGold hN11a hN11b hN11c
    (asc82Sec5Inputs13_of_inputs15 h3 h7 i)

end CFSG.OddStandard.SmallF3.Omega
