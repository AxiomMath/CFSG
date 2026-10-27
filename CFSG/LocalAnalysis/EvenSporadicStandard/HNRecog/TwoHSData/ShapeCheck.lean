module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def primeOrderOK (p : ℕ) (t : Table) : Bool :=
  tblEq 1408 (powT 1408 p t) (idT 1408) && !tblEq 1408 t (idT 1408)

@[expose] def commWordsOK (ws : List (List ℕ)) (t : Table) : Bool :=
  ws.all fun w => commTT 1408 (tabW w) t

@[expose] def commPairsOK (us vs : List (List ℕ)) : Bool :=
  us.all fun u => vs.all fun v => commTT 1408 (tabW u) (tabW v)

@[expose] def wordsInOK (L : Array Table) (ws : List (List ℕ)) : Bool :=
  ws.all fun w => memT 1408 L (tabW w)

@[expose, noinline] def trivInterOK (idt : Table) (LV LA : Array Table) : Bool :=
  LV.all fun v => tblEq 1408 v idt || !memT 1408 LA v

@[expose, noinline] def powOneOK (e : ℕ) (idt : Table) (L : Array Table) : Bool :=
  L.all fun s => tblEq 1408 (powT 1408 e s) idt

@[expose, noinline] def normGensOK (LN : Array Table) (cs ns : List (List ℕ)) : Bool :=
  cs.all fun c =>
    let tc := tabW c
    let ti := invT 1408 tc
    invOK 1408 tc ti && ns.all fun n =>
      let tn := tabW n
      memT 1408 LN (conjT 1408 tc ti tn) && memT 1408 LN (conjT 1408 ti tc tn)

@[expose] def commutatorEqOK (tu tv ta : Table) : Bool :=
  invOK 1408 tu (invT 1408 tu) && invOK 1408 tv (invT 1408 tv) &&
    tblEq 1408 (compT 1408 (compT 1408 (compT 1408 tu tv) (invT 1408 tu)) (invT 1408 tv)) ta

end CFSG.EvenSporadicStandard.HNRecog
