module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWAdmData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native

@[expose] def admW (w : List (Array Nat)) : Bool :=
  sqW w && (evR w 32 == 32) && (evR w 64 == 85) &&
  (List.range 32).all (fun c => decide (evR w c < 32)) &&
  (((List.range 32).filter fun c => evR w c == c).length == 8) &&
  (List.range 32).any fun c => c != 0 && c != 21 && mulC c c == 0 && evR w c == c

@[expose] def admTabOK (i : Nat) : Bool :=
  decide (admArr[i]!.size = 128) && isInvA 128 admArr[i]! (invCand 128 admArr[i]!) &&
  inPg admArr[i]! && admW [admArr[i]!]

@[expose] def admIsoOK (i : Nat) : Bool :=
  let p := admArr[i]!
  let f := admIso[i]!
  decide (f.size = 32) && (f[0]! == 0) && (f[21]! == 21) &&
  (List.range 32).all (fun k => decide (f[k]! < 128) && (p[f[k]!]! == f[k]!)) &&
  (List.range 32).all (fun a => (List.range 32).all fun b =>
      f[mulE0 a b]! == mulC f[a]! f[b]!) &&
  (List.range 32).all (fun a => (List.range 32).all fun b => a == b || f[a]! != f[b]!) &&
  (List.range 128).all (fun c => p[c]! != c || (List.range 32).any fun k => f[k]! == c) &&
  (((List.range 128).filter fun c => (List.range 128).all fun g =>
      p[g]! != g || mulC c g == mulC g c).length == 8)

@[expose] def admCheck : Bool :=
  decide (admArr.size = 60) && decide (admIso.size = 60) &&
  (List.range 60).all admTabOK && (List.range 60).all admIsoOK &&
  (List.range 60).all (fun i => (List.range 60).all fun j =>
      i == j || !eqA 128 admArr[i]! admArr[j]!) &&
  (countW admW blocksPg [] == 60)

end CFSG.EvenSporadicStandard.Fin76b.W16
