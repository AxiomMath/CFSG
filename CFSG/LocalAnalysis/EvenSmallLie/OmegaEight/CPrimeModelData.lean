module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ShapeCPrimeData

public section

namespace CFSG.EvenSmallLie.OmegaEight.CPrimeModel

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar (bmulVec)
open CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.Stage1.Model
open CFSG.EvenSmallLie.OmegaEight.CPrime (reflRows)

@[expose] def sigArr : Eps → Array ℕ
  | .plus => OmegaEight.copy0Arr OmegaEight.genArrs[9]!
  | .minus => OmegaEightMinus.genArrs[10]!

@[expose] def sigCheck (ε : Eps) : Bool :=
  isInvA (deg ε) (sigArr ε) (invCand (deg ε) (sigArr ε)) &&
    eqA (deg ε) (compA (deg ε) (sigArr ε) (sigArr ε)) (idA (deg ε)) &&
    allLt 64 (fun y => eqA (deg ε) (conjA (deg ε) (sigArr ε) (psiArr ε y))
      (psiArr ε (bmulVec 6 6 (reflRows ε (n0 ε)) y))) &&
    allLt 6 (fun k => memU ε (conjA (deg ε) (sigArr ε) (uArr ε k)))

@[expose] def wArr : ℕ → Array ℕ
  | 0 => idA 360
  | 1 => OmegaEight.genArrs[9]!
  | 2 => OmegaEight.genArrs[8]!
  | 3 => compA 360 OmegaEight.genArrs[8]! OmegaEight.genArrs[9]!
  | 4 => compA 360 OmegaEight.genArrs[8]! OmegaEight.genArrs[8]!
  | _ => compA 360 (compA 360 OmegaEight.genArrs[8]! OmegaEight.genArrs[8]!)
      OmegaEight.genArrs[9]!

@[expose] def cosetCheck : Bool :=
  allLt 6 (fun i => isInvA 360 (wArr i) (invCand 360 (wArr i)) && memA .plus (wArr i)) &&
    allLt 6 (fun i => allLt 6 fun j =>
      i == j || !memOmPlus (compA 360 (wArr j) (invCand 360 (wArr i)))) &&
    !memOmPlus (compA 360 (wArr 2) (wArr 2)) && !memOmPlus (compA 360 (wArr 4) (wArr 4)) &&
    allLt 4 (fun j => decide (120 ≤ (wArr (j + 2))[0]!)) &&
    allLt 360 (fun p => decide ((OmegaEight.genArrs[9]!)[p]! < 120) == decide (p < 120)) &&
    eqA 360 (compA 360 OmegaEight.genArrs[9]! OmegaEight.genArrs[9]!) (idA 360) &&
    eqA 360 (OmegaEight.conjArr (wArr 2) (wArr 3)) OmegaEight.genArrs[9]! &&
    eqA 360 (OmegaEight.conjArr (wArr 4) (wArr 5)) OmegaEight.genArrs[9]!

@[expose] def minusCheck : Bool :=
  !memL .minus OmegaEightMinus.genArrs[10]! &&
    eqA 136 (compA 136 OmegaEightMinus.genArrs[10]! OmegaEightMinus.genArrs[10]!) (idA 136)

end CFSG.EvenSmallLie.OmegaEight.CPrimeModel
