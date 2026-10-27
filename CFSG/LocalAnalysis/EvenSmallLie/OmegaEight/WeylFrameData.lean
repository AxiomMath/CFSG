module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylCoordData

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def reflArrs : Array (Array ℕ) := ((List.range 240).map reflArr).toArray

@[expose] def equivCheckWith (RA : Array (Array ℕ)) : Bool :=
  allLt 240 fun a => allLt 240 fun r =>
    eqA 240 (compA 240 (compA 240 RA[a]! RA[r]!) RA[a]!) RA[(RA[a]!)[r]!]!

@[expose] def equivCheck : Bool := equivCheckWith reflArrs

@[expose] def frame16 : List ℕ := [0, 1, 2, 3, 52, 53, 54, 55, 88, 89, 90, 91, 108, 109, 110, 111]

@[expose] def negSet (x : Array ℕ) : List ℕ := (List.range 240).filter fun r => x[r]! == negArr[r]!

@[expose] def frameCheckWith (RA FA : Array (Array ℕ)) : Bool :=
  allLt 240 (fun r => memE1 FA RA[r]! == frame16.contains r) &&
    allLt 256 (fun m => frameMaskOf FA[m]! == m) &&
    allLt 256 (fun m => allLt 8 fun i =>
      (FA[m]!)[keyPts.getD i 0]! ==
        if m.testBit i then negArr[keyPts.getD i 0]! else keyPts.getD i 0) &&
    allLt 8 (fun i => negSet RA[keyPts.getD i 0]! ==
      [keyPts.getD i 0, negArr[keyPts.getD i 0]!].mergeSort (fun a b => decide (a ≤ b))) &&
    allLt 8 (fun i => allLt 8 fun j => i == j || negSet FA[2 ^ i + 2 ^ j]! ==
      [keyPts.getD i 0, negArr[keyPts.getD i 0]!, keyPts.getD j 0,
        negArr[keyPts.getD j 0]!].mergeSort (fun a b => decide (a ≤ b))) &&
    allLt 256 (fun m => framePop m != 4 || ((fixCount 240 FA[m]! == 24) == frameIsPlane m))

@[expose] def frameCheck : Bool := frameCheckWith reflArrs frameArrs

@[expose] def singerArr : Array ℕ :=
  #[
    53, 1, 2, 54, 197, 157, 194, 154, 189, 165, 186, 162, 4, 35, 32, 7, 9, 30, 29, 10, 117, 237,
    114, 234, 213, 141, 210, 138, 196, 156, 195, 155, 188, 164, 187, 163, 28, 11, 8, 31, 33, 6,
    5, 34, 116, 236, 115, 235, 212, 140, 211, 139, 109, 89, 90, 110, 192, 199, 152, 159, 198,
    193, 158, 153, 92, 107, 104, 95, 97, 102, 101, 98, 184, 191, 160, 167, 190, 185, 166, 161,
    100, 99, 96, 103, 105, 94, 93, 106, 0, 52, 55, 3, 112, 232, 119, 239, 208, 136, 215, 143,
    118, 238, 113, 233, 214, 142, 209, 137, 88, 108, 111, 91, 180, 178, 40, 16, 36, 12, 148,
    146, 182, 183, 78, 62, 74, 58, 150, 151, 176, 177, 60, 76, 56, 72, 144, 145, 181, 179, 18,
    42, 14, 38, 149, 147, 49, 25, 220, 218, 228, 226, 45, 21, 87, 71, 222, 223, 230, 231, 83,
    67, 69, 85, 216, 217, 224, 225, 65, 81, 27, 51, 221, 219, 229, 227, 23, 47, 44, 20, 124,
    122, 132, 130, 48, 24, 82, 66, 126, 127, 134, 135, 86, 70, 64, 80, 120, 121, 128, 129, 68,
    84, 22, 46, 125, 123, 133, 131, 26, 50, 204, 202, 37, 13, 41, 17, 172, 170, 206, 207, 75,
    59, 79, 63, 174, 175, 200, 201, 57, 73, 61, 77, 168, 169, 205, 203, 15, 39, 19, 43, 173, 171]

@[expose] def singerList : List ℕ := [0, 2, 4, 6, 3, 1, 7, 5]

@[expose] def flipList : List ℕ := [1, 0, 3, 2, 4, 5, 6, 7]

@[expose] def powArr' (x : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 240
  | k + 1 => compA 240 x (powArr' x k)

@[expose] def singerCheck : Bool :=
  isInvA 240 singerArr (invCand 240 singerArr) && siftW singerArr &&
    isId (powArr' singerArr 7) &&
    allLt 8 (fun i => singerArr[keyPts.getD i 0]! == keyPts.getD (singerList.getD i 0) 0) &&
    allLt 8 (fun i => (signArrs[5]!)[keyPts.getD i 0]! ==
      if i < 4 then negArr[keyPts.getD (flipList.getD i 0) 0]! else keyPts.getD i 0)

end CFSG.EvenSmallLie.OmegaEight.Weyl
