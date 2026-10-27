module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylFrameData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def dPairs : List (ℕ × ℕ) :=
  (List.range 8).flatMap fun i => ((List.range 8).filter (i < ·)).map fun j => (i, j)

@[expose] def memE (SA : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  let j := x[112]! - 112
  decide (112 ≤ x[112]!) && ((framePop (2 * j) % 2 == 0 && eqA 240 x SA[2 * j]!) ||
    (framePop (2 * j + 1) % 2 == 0 && eqA 240 x SA[2 * j + 1]!))

@[expose] def permMask (σ : Equiv.Perm (Fin 8)) (m : ℕ) : ℕ :=
  frameEncode (permVec σ (frameDecode m))

@[expose] def permVecL (σ : Equiv.Perm (Fin 8)) (x : List ℤ) : List ℤ :=
  (List.finRange 8).map fun k => x.getD (σ.symm k : ℕ) 0

@[expose] def dCheckWith (RA SA : Array (Array ℕ)) : Bool :=
  (List.range 240).all (fun r => decide (r < 112) || (List.range 256).all fun m =>
    !(framePop m % 2 == 0) || m == 0 || (SA[m]!)[r]! != r) &&
  allLt 240 (fun r => memE SA (compA 240 RA[1]! RA[r]!) == decide (r < 4)) &&
  dPairs.all (fun p => [0, 1].all fun s => (List.range 256).all fun m => !(framePop m % 2 == 0) ||
    eqA 240 (compA 240 (compA 240 RA[4 * dPairs.idxOf p + s]! SA[m]!) RA[4 * dPairs.idxOf p + s]!)
      SA[permMask (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) m]!) &&
  allLt 240 (fun r => rootIdx (rootVec r) == r) && rootList.length == 240 &&
  allLt 240 (fun r => (rootVec r).length == 8) &&
  dPairs.all (fun p => allLt 240 (fun r => decide
      (rootIdx (permVecL (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2)) (rootVec r)) < 240)) &&
    eqA 240 (permArr (Equiv.swap (Fin.ofNat 8 p.1) (Fin.ofNat 8 p.2))) RA[4 * dPairs.idxOf p + 1]!)

@[expose] def dCheck : Bool := dCheckWith reflArrs signArrs

end CFSG.EvenSmallLie.OmegaEight.Weyl
