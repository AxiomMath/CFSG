module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End520
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B6b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

structure Asc82Sec5Inputs8 : Prop where
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
  l516a : Asc82Lemma516a
  l518b : Asc82Lemma518b
  l519 : Asc82Lemma519
  par : Asc82Lemma518Parity
  corIIIq : Asc82CorIIIq

theorem asc82Sec5Inputs6_of_inputs8 (h3 : Asc82Sec3Results) (hGold : GoldStmt)
    (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) (i : Asc82Sec5Inputs8) :
    Asc82Sec5Inputs6 :=
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
    l515S := i.l515S
    heart := i.heart
    l518b := i.l518b
    l519 := i.l519
    end520 := fun h517 h518b h519 =>
      asc82End520_of hGold hN11a hN11b hN11c h514 i.l516a
        (asc82SylowContain_of h514 i.l516a i.par h517) h517 h518b h519
    corIIIq := i.corIIIq }

theorem aschOmega6MinusZ2_of_inputs8
    (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (hGold : GoldStmt)
    (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) (i : Asc82Sec5Inputs8) :
    AschOmega6MinusZ2 :=
  aschOmega6MinusZ2_of_inputs6 h3 h34a h7 hZ hO
    (asc82Sec5Inputs6_of_inputs8 h3 hGold hN11a hN11b hN11c i)

end CFSG.OddStandard.SmallF3.Omega
