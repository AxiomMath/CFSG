module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWChain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWRepData

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def sqW (w : List (Array Nat)) : Bool := baseArr.all fun b => evR w (evR w b) == b

@[expose] def neOneW (w : List (Array Nat)) : Bool := baseArr.any fun b => evR w b != b

@[expose] def involW (w : List (Array Nat)) : Bool := sqW w && neOneW w

@[expose] def commW (r : Array Nat) (w : List (Array Nat)) : Bool :=
  baseArr.all fun b => evR w r[b]! == r[evR w b]!

@[expose] def fixCntW (w : List (Array Nat)) : Nat :=
  ((List.range 128).filter fun i => evR w i == i).length

@[expose] def fixSqW (w : List (Array Nat)) : Nat :=
  ((List.range 128).filter fun i => evR w i == i && mulC i i == tC).length

@[expose] def repCheck : Bool :=
  decide (repArrs.size = 9) && decide (fpTab.size = 9) && decide (centTab.size = 9) &&
  (List.range 9).all fun j =>
    let r := repArrs[j]!
    isInvA 128 r (invCand 128 r) && eqA 128 (compA 128 r r) (idA 128) && inPg r &&
      neOneW [r] && (fixCntW [r] == (fpTab[j]!).1) && (fixSqW [r] == (fpTab[j]!).2)

@[expose] def fpDistinct : Bool :=
  (List.range 9).all fun j => (List.range 9).all fun j' => j == j' || fpTab[j]! != fpTab[j']!

@[expose] def sumCheck : Bool :=
  (List.range 9).all (fun j => centTab[j]! != 0 && 3317760 % centTab[j]! == 0) &&
    ((List.range 9).map fun j => 3317760 / centTab[j]!).sum == 10575

@[expose] def centCheck : Bool :=
  (List.range 9).all fun j => countW (commW repArrs[j]!) blocksPg [] == centTab[j]!

@[expose] def eqNatB (a b : ℕ) : Bool := a == b

theorem eqNatB_iff {a b : ℕ} : eqNatB a b = true ↔ a = b := by
  unfold eqNatB
  exact beq_iff_eq

@[expose] def involCheck : Bool := eqNatB (countW involW blocksPg []) 10575

@[expose] def zD (i : Nat) : Nat :=
  if i < 4 then (4 - i) % 4 else 4 + ((1 + 4 - (i - 4)) % 4)

@[expose] def sameSet (S T : Array Nat) : Bool :=
  S.all (fun x => T.contains x) && T.all (fun x => S.contains x) && S.size == T.size

@[expose] def imgSet (g : Array Nat) (S : Array Nat) : Array Nat := S.map fun x => g[x]!

@[expose] def x45Check : Bool :=
  decide (x45Sets.size = 45) && decide (x45Par.size = 45) &&
  (List.range 45).all (fun i => decide (x45Sets[i]!.size = 8) &&
      x45Sets[i]!.all (fun x => decide (x < 128)) &&
      (List.range 8).all fun k => (List.range 8).all fun k' =>
        k == k' || (x45Sets[i]!)[k]! != (x45Sets[i]!)[k']!) &&
  (List.range 45).all (fun i => (List.range 45).all fun i' => i == i' || !sameSet x45Sets[i]! x45Sets[i']!) &&
  (List.range 44).all (fun i' => decide (x45Par[i' + 1]!.1 < i' + 1) &&
      decide (x45Par[i' + 1]!.2 < 36) &&
      sameSet (imgSet sgsArr[x45Par[i' + 1]!.2]! x45Sets[x45Par[i' + 1]!.1]!) x45Sets[i' + 1]!) &&
  (List.range 36).all (fun gi => (List.range 45).all fun i =>
      (List.range 45).any fun i' => sameSet (imgSet sgsArr[gi]! x45Sets[i]!) x45Sets[i']!) &&
  (List.range 9).all fun j => ((List.range 45).filter fun i =>
      sameSet (imgSet repArrs[j]! x45Sets[i]!) x45Sets[i]!).length == fix45Tab[j]!

@[expose] def zetaCheck : Bool :=
  (List.range 128).all fun c => (repArrs[8]!)[c]! == ixP (zD (decD c)) (c % 32)

@[expose] def twistCheck : Bool :=
  decide (b0Idx < 128) && ((repArrs[8]!)[b0Idx]! == b0Idx) && (mulC b0Idx b0Idx == tC) &&
    (List.range 128).all fun i =>
      (repArrs[7]!)[i]! == (repArrs[8]!)[mulC (mulC b0Idx i) (invC b0Idx)]!

@[expose] def fusCheck : Bool :=
  [4, 7, 8].all fun j =>
    decide (fusTab[j]! < 128) && ((repArrs[j]!)[fusTab[j]!]! == mulC fusTab[j]! tC)

@[expose] def check27821 : Bool := repCheck && fpDistinct && sumCheck && centCheck && involCheck

@[expose] def check27822 : Bool := x45Check && zetaCheck && twistCheck && fusCheck

end CFSG.EvenSporadicStandard.Fin76b.W16
