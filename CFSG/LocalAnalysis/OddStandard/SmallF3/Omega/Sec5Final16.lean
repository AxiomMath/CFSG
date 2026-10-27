module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final15
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

structure Asc82Sec5Inputs16 : Prop where
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
  qcentExp : Asc82FactQCentExp6
  qbCent : Asc82FactQBCent6
  cent6 : Asc82FactOm6CentD
  nrank6 : Asc82FactOm6NRank
  par5 : Asc82FactOm6Par
  corIIIq : Asc82CorIIIq

theorem asc82Sec5Inputs15_of_inputs16 (h3 : Asc82Sec3Results)
    (h34a : Asc82Lemma34a) (h7 : AschOmega7) (i : Asc82Sec5Inputs16) : Asc82Sec5Inputs15 :=
  have h51 : Asc82Lemma51 := asc82Lemma51_of h7 h3.l38 h3.l311
  have h52a : Asc82Lemma52a := asc82Lemma52a_of h3.l33 h51
  have h52b : Asc82Lemma52b := asc82Lemma52b_of h52a
  have h53 : Asc82Lemma53 := asc82Lemma53_of h3.l36 h52a h52b i.tab
  have h54 : Asc82Lemma54 := asc82Lemma54_of h3.l36 h3.l37 h52a h52b h53 i.tab
  have hy : Sec5B59Hyp := ⟨h3.l36, h3.l37, h52b, h53, i.tab, h54, i.l58b⟩
  have h510 : Asc82Lemma510 := asc82Lemma510_of hy i.l58d asc82Fact59_holds i.f510
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
    m1 := i.m1
    f7 := i.f7
    l511csl := asc82Lemma511CSL_of h34a h3.l36 h3.l37 h52a h52b h53 i.tab i.l58d h510
      i.facts6.pockets i.qcentExp i.qbCent
    cent6 := i.cent6
    nrank6 := i.nrank6
    par5 := i.par5
    corIIIq := i.corIIIq }

theorem aschOmega6MinusZ2_of_inputs16
    (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (hGold : GoldStmt)
    (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) (i : Asc82Sec5Inputs16) :
    AschOmega6MinusZ2 :=
  aschOmega6MinusZ2_of_inputs15 h3 h34a h7 hZ hO hGold hN11a hN11b hN11c
    (asc82Sec5Inputs15_of_inputs16 h3 h34a h7 i)

end CFSG.OddStandard.SmallF3.Omega
