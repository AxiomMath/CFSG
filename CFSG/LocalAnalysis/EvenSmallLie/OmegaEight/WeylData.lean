module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylDefs
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def posRoots : List ℕ :=
  [0, 1, 4, 5, 8, 9, 12, 13, 16, 17, 20, 21, 24, 25, 28, 29, 32, 33, 36, 37, 40, 41, 44, 45, 48,
    49, 52, 53, 56, 57, 60, 61, 64, 65, 68, 69, 72, 73, 76, 77, 80, 81, 84, 85, 88, 89, 92, 93, 96,
    97, 100, 101, 104, 105, 108, 109, 112, 115, 117, 118, 121, 122, 124, 127, 129, 130, 132, 135,
    136, 139, 141, 142, 145, 146, 148, 151, 152, 155, 157, 158, 160, 163, 165, 166, 169, 170, 172,
    175, 177, 178, 180, 183, 184, 187, 189, 190, 192, 195, 197, 198, 201, 202, 204, 207, 208, 211,
    213, 214, 217, 218, 220, 223, 225, 226, 228, 231, 232, 235, 237, 238]

@[expose] def reflS : Array (Array ℕ) := (posRoots.map reflArr).toArray

@[expose] def wBase : List (Fin 240) := [1, 0, 53, 52, 89, 88, 109, 108]

@[expose] def sgsRoots : List ℕ := [0, 2, 30, 54, 74, 90, 102, 175, 52, 173, 110, 88, 108]

@[expose] def wS : Array (Array ℕ) := (sgsRoots.map reflArr).toArray

@[expose] def wWords : Array (List ℤ) := (List.replicate 13 []).toArray

@[expose] def wChainCheck : Bool :=
  rawChainOK 240 (wS.extract 0 13) wS (wBase.map Fin.val).toArray wWords 4 &&
    rawOrbitSizes 240 wS (wBase.map Fin.val).toArray == [240, 126, 60, 2, 24, 2, 2, 2] &&
    allLt 240 fun r =>
      siftA 240 (rawLevels 240 wS (wBase.map Fin.val).toArray) (wBase.map Fin.val).toArray 0
        (reflArr r)

@[expose] def fixCount (n : ℕ) (t : Array ℕ) : ℕ := (List.range n).countP fun i => t[i]! == i

@[expose] def reflCheck : Bool :=
  allLt 240 (fun r => isInvA 240 (reflArr r) (reflArr r) && fixCount 240 (reflArr r) == 126 &&
    decide (negArr[r]! < 240) && eqA 240 (reflArr (negArr[r]!)) (reflArr r) &&
    (List.range 120).any fun i => eqA 240 (reflArr r) reflS[i]!) &&
  isInvA 240 negArr negArr && fixCount 240 negArr == 0 &&
  allLt 240 (fun r => eqA 240 (compA 240 negArr (reflArr r)) (compA 240 (reflArr r) negArr))

end CFSG.EvenSmallLie.OmegaEight.Weyl
