module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888G4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5LSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

structure Asc82Sec5Inputs6 : Prop where
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
  l515S : Asc82Lemma515Setting
  heart : Asc82HeartDict
  l518b : Asc82Lemma518b
  l519 : Asc82Lemma519
  end520 : Asc82End520
  corIIIq : Asc82CorIIIq

theorem asc82Sec5Inputs5_of_inputs6
    (h3 : Asc82Sec3Results) (i : Asc82Sec5Inputs6) : Asc82Sec5Inputs5 :=
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
    l515S := i.l515S
    fuse := asc82Fact517Fuse_of_heart
      (asc82Lemma514_of h3.l37 (asc82Lemma513_of h3.l36 h3.l37 i.f513)) i.heart
    swap := asc82FactSwap6_of_certs
    l518b := i.l518b
    l519 := i.l519
    end520 := i.end520
    corIIIq := i.corIIIq }

theorem aschOmega6MinusZ2_of_inputs6
    (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (i : Asc82Sec5Inputs6) :
    AschOmega6MinusZ2 :=
  aschOmega6MinusZ2_of_inputs5 h3 h34a h7 hZ hO (asc82Sec5Inputs5_of_inputs6 h3 i)

end CFSG.OddStandard.SmallF3.Omega
