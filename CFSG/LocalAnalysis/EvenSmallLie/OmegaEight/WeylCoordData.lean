module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def siftW (x : Array ℕ) : Bool :=
  siftA 240 (rawLevels 240 wS (wBase.map Fin.val).toArray) (wBase.map Fin.val).toArray 0 x

@[expose] def tableOK (A : Array (Array ℕ)) (p : ℕ → Bool) (sgn : ℕ → ℕ) : Bool :=
  (List.range 256).all (fun a => !p a || (isInvA 240 A[a]! A[a]! && siftW A[a]! &&
    ((240 - fixCount 240 A[a]!) / 2) % 2 == sgn a)) &&
  (List.range 256).all (fun a => !p a || (List.range 256).all fun b => !p b ||
    (eqA 240 (compA 240 A[a]! A[b]!) A[a ^^^ b]! && (a == b || !eqA 240 A[a]! A[b]!)))

@[expose] def coordCheckWith (SA FA : Array (Array ℕ)) : Bool :=
  tableOK FA (fun _ => true) (fun a => framePop a % 2) &&
    tableOK SA (fun a => framePop a % 2 == 0) (fun _ => 0) &&
    allLt 8 (fun i => eqA 240 FA[2 ^ i]! (reflArr (keyPts.getD i 0))) &&
    eqA 240 FA[255]! negArr && eqA 240 SA[255]! negArr &&
    [0, 2, 4, 6].all (fun i => eqA 240 SA[2 ^ i + 2 ^ (i + 1)]! FA[2 ^ i + 2 ^ (i + 1)]!) &&
    eqA 240 (permArr (Equiv.swap 0 1)) s0Arr

@[expose] def coordCheck : Bool := coordCheckWith signArrs frameArrs

end CFSG.EvenSmallLie.OmegaEight.Weyl
