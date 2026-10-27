module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Certificates.Native

@[expose] def candSet (k : Nat) : List Nat :=
  (List.range 128).filter fun c =>
    c != 0 && c != tC && mulC c c == mulC baseArr[k]! baseArr[k]! &&
      (List.range k).all fun j => commC c baseArr[j]! == commC baseArr[k]! baseArr[j]!

@[expose] def tableCheck : Bool :=
  (List.range 128).all (fun a => (List.range 128).all fun b => decide (mulC a b < 128)) &&
  (List.range 128).all (fun a => mulC 0 a == a && mulC a 0 == a && mulC a (invC a) == 0 &&
      mulC (invC a) a == 0 && decide (invC a < 128) && (mulC a a == 0 || mulC a a == tC)) &&
  (List.range 128).all (fun c =>
      !((List.range 128).all fun d => mulC c d == mulC d c) || c == 0 || c == tC) &&
  (List.range 128).all (fun d => mulC tC d == mulC d tC) &&
  mulC tC tC == 0 && tC != 0 && decide (tC < 128)

@[expose] def autCheck : Bool :=
  sgsArr.all fun s =>
    decide (s.size = 128) && (List.range 128).all (fun a => decide (s[a]! < 128)) &&
    (List.range 128).all (fun a => (List.range 128).all fun b => s[mulC a b]! == mulC s[a]! s[b]!) &&
    (List.range 128).all fun a => (List.range 128).any fun b => s[b]! == a

@[expose] def chainCheck : Bool :=
  rawChainOK 128 (sgsArr.extract 0 36) sgsArr baseArr wordsArr 4 &&
    (rawOrbitSizes 128 sgsArr baseArr).prod == 3317760

@[expose] def genCheck : Bool :=
  decide (baseArr.size = 6) && decide (genElems.size = 128) && decide (genPar.size = 128) &&
    decide (genGen.size = 128) && (genElems[0]! == 0) &&
    (List.range 128).all (fun j => decide (genElems[j]! < 128)) &&
    (List.range 128).all (fun c => (List.range 128).any fun j => genElems[j]! == c) &&
    (List.range 127).all (fun j' => let j := j' + 1;
      decide (genPar[j]! < j) && decide (genGen[j]! < 6) &&
        (mulC genElems[genPar[j]!]! baseArr[genGen[j]!]! == genElems[j]!)) &&
    baseArr.all (fun b => decide (b < 128))

@[expose] def candCheck : Bool :=
  ((List.range 6).map fun k => (candSet k).length).prod == 3317760

@[expose] def check27820 : Bool :=
  tableCheck && autCheck && chainCheck && genCheck && candCheck

end CFSG.EvenSporadicStandard.Fin76b.W16
