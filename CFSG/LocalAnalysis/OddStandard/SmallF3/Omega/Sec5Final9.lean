module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Final8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Fin518

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Goldschmidt CFSG.GH74.GLS.Th2.P412

structure Asc82Sec5Inputs9 : Prop where
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
  cent6 : Asc82FactOm6CentD
  nrank6 : Asc82FactOm6NRank
  l519 : Asc82Lemma519
  par : Asc82Lemma518Parity
  corIIIq : Asc82CorIIIq

theorem asc82Lemma518b_of_inputs9
    (h3 : Asc82Sec3Results)
    (h34a : Asc82Lemma34a) (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside)
    (i : Asc82Sec5Inputs9) : Asc82Lemma518b := by
  have h51 : Asc82Lemma51 := asc82Lemma51_of h7 h3.l38 h3.l311
  have h52a : Asc82Lemma52a := asc82Lemma52a_of h3.l33 h51
  have h52b : Asc82Lemma52b := asc82Lemma52b_of h52a
  have h53 : Asc82Lemma53 := asc82Lemma53_of h3.l36 h52a h52b i.tab
  have h54 : Asc82Lemma54 := asc82Lemma54_of h3.l36 h3.l37 h52a h52b h53 i.tab
  have h55 : Asc82Lemma55 := asc82Lemma55_of h3.l36 h3.l37 h52a h52b h53 h54 hO i.tab
  have hs56 : Asc82Step56 := asc82Step56_of h52b h53 h54 h3.l37 hZ i.tab i.tab56
  have h56 : Asc82Lemma56 := asc82Lemma56_of h52b h55 i.tab hs56
  have hy : Sec5B59Hyp := ⟨h3.l36, h3.l37, h52b, h53, i.tab, h54, i.l58b⟩
  have h510 : Asc82Lemma510 := asc82Lemma510_of hy i.l58d asc82Fact59_holds i.f510
  have h512b : Asc82Lemma512b :=
    asc82Lemma512b_of h34a hy h52a i.l58d asc82Fact59_holds i.f510 i.facts6.pockets
      i.facts6.qcent i.facts6.frame i.facts6.outZeta
  have h512K : Asc82Lemma512K := asc82Lemma512K_of i.fact512K
  have h512H : Asc82Lemma512H :=
    asc82Lemma512H_of h3.l36 h3.l37 h52b h53 i.tab h510 i.fact512H
  have h513 : Asc82Lemma513 := asc82Lemma513_of h3.l36 h3.l37 i.f513
  have h514 : Asc82Lemma514 := asc82Lemma514_of h3.l37 h513
  have h515 : Asc82Lemma515a ∧ Asc82Lemma515b ∧ Asc82Lemma515c :=
    asc82Lemma515_of i.l515S asc82FactPocketsTwo_of h514 h52a h52b h56 hZ i.factB h512b h512K
      h512H i.tab
  have h517 : Asc82Lemma517 :=
    asc82Lemma517_of h3.l37 h513 h514 h515.2.1 h515.2.2 (asc82Fact517Fuse_of_heart h514 i.heart)
      asc82FactSwap6_of_certs
  exact asc82Lemma518b_of h514 h515.2.2 i.l516a h517 i.par h52a h3.l37 i.cent6 i.nrank6

theorem asc82Sec5Inputs8_of_inputs9
    (h3 : Asc82Sec3Results)
    (h34a : Asc82Lemma34a) (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside)
    (i : Asc82Sec5Inputs9) : Asc82Sec5Inputs8 :=
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
    l516a := i.l516a
    l518b := asc82Lemma518b_of_inputs9 h3 h34a h7 hZ hO i
    l519 := i.l519
    par := i.par
    corIIIq := i.corIIIq }

theorem aschOmega6MinusZ2_of_inputs9
    (h3 : Asc82Sec3Results) (h34a : Asc82Lemma34a)
    (h7 : AschOmega7) (hZ : Asc82ZExists) (hO : Asc82Outside) (hGold : GoldStmt)
    (hN11a : S_N11a) (hN11b : S_N11b) (hN11c : S_N11c) (i : Asc82Sec5Inputs9) :
    AschOmega6MinusZ2 :=
  aschOmega6MinusZ2_of_inputs8 h3 h34a h7 hZ hO hGold hN11a hN11b hN11c
    (asc82Sec5Inputs8_of_inputs9 h3 h34a h7 hZ hO i)

end CFSG.OddStandard.SmallF3.Omega
