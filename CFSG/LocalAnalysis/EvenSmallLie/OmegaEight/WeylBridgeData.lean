module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylDefs

public section

namespace CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def wordArr : List ℕ → Array ℕ
  | [] => idA 240
  | r :: l => compA 240 (reflArr r) (wordArr l)

@[expose] def pairArr : Array ℕ :=
  #[
    1, 9, 9, 1, 51, 27, 27, 51, 46, 38, 38, 46, 106, 98, 98, 106, 117, 95, 95, 117, 87, 63, 63,
    87, 68, 76, 76, 68, 34, 42, 42, 34, 31, 55, 55, 31, 91, 115, 115, 91, 100, 108, 108, 100,
    70, 78, 78, 70, 85, 59, 59, 85, 13, 5, 5, 13, 73, 65, 65, 73, 86, 60, 60, 86, 116, 92, 92,
    116, 103, 111, 111, 103, 84, 56, 56, 84, 75, 67, 67, 75, 105, 97, 97, 105, 88, 114, 114, 88,
    15, 7, 7, 15, 45, 37, 37, 45, 28, 54, 54, 28, 50, 24, 24, 50, 33, 41, 41, 33, 3, 11, 11, 3,
    57, 69, 119, 102, 107, 90, 72, 80, 47, 30, 12, 20, 16, 8, 26, 43, 49, 32, 18, 10, 14, 22,
    36, 53, 74, 82, 96, 113, 94, 109, 61, 71, 19, 2, 48, 40, 44, 52, 6, 23, 104, 112, 66, 83,
    62, 79, 93, 101, 118, 110, 58, 77, 64, 81, 99, 89, 4, 21, 39, 29, 25, 35, 17, 0, 0, 17, 35,
    25, 29, 39, 21, 4, 89, 99, 81, 64, 77, 58, 110, 118, 101, 93, 79, 62, 83, 66, 112, 104, 23,
    6, 52, 44, 40, 48, 2, 19, 71, 61, 109, 94, 113, 96, 82, 74, 53, 36, 22, 14, 10, 18, 32, 49,
    43, 26, 8, 16, 20, 12, 30, 47, 80, 72, 90, 107, 102, 119, 69, 57]

@[expose] def pairRepArr : Array ℕ :=
  #[
    175, 0, 145, 108, 168, 53, 150, 89, 125, 1, 131, 109, 122, 52, 132, 88, 124, 174, 130, 144,
    123, 169, 133, 151, 101, 172, 126, 5, 96, 171, 121, 32, 129, 104, 28, 173, 134, 93, 9, 170,
    147, 105, 29, 127, 148, 92, 8, 120, 146, 128, 100, 4, 149, 135, 97, 33, 73, 112, 162, 49,
    61, 142, 156, 21, 164, 57, 154, 77, 24, 113, 44, 143, 118, 56, 136, 76, 25, 163, 45, 157,
    119, 165, 137, 155, 72, 48, 60, 20, 84, 167, 117, 36, 65, 158, 140, 17, 138, 81, 13, 166,
    40, 159, 115, 68, 152, 80, 12, 116, 41, 141, 161, 69, 153, 139, 85, 37, 64, 16, 160, 114]

@[expose] def pArr (g : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 120) fun j => pairArr[g[pairRepArr[j.val]!]!]!

@[expose] def pairCheck : Bool :=
  allLt 240 (fun x => decide (pairArr[x]! < 120) && pairArr[negArr[x]!]! == pairArr[x]!) &&
    allLt 240 (fun x => allLt 240 fun y =>
      pairArr[x]! != pairArr[y]! || y == x || y == negArr[x]!) &&
    allLt 120 (fun j => decide (pairRepArr[j]! < 240) && pairArr[pairRepArr[j]!]! == j)

@[expose] def omWords : List (List ℕ) :=
  [[101, 172, 29, 127], [101, 126, 28, 173], [175, 0, 129, 104], [175, 145, 124, 130],
    [175, 145, 164, 154], [175, 168, 129, 134], [175, 145, 168, 150], [175, 129, 164, 138]]

@[expose] def frameRootList : List ℕ := [1, 0, 53, 52, 89, 88, 109, 108]

@[expose] def zWordCheck : Bool := eqA 240 (wordArr frameRootList) negArr

@[expose] def omCheck : Bool :=
  allLt 8 fun i => eqA 120 (pArr (wordArr (omWords.getD i []))) (copy0Arr genArrs[i]!)

@[expose] def sZeroCheck : Bool :=
  !(siftA 120 (rawLevels 120 omega1S (omega1Base.map Fin.val).toArray)
    (omega1Base.map Fin.val).toArray 0 (pArr (reflArr 1)))

@[expose] def trialityCheck : Bool :=
  let u := compA 240 (wordArr (omWords.getD 4 [])) (wordArr (omWords.getD 6 []))
  let y := compA 240 (wordArr (omWords.getD 6 [])) (wordArr (omWords.getD 0 []))
  eqA 240 (compA 240 u u) (idA 240) && !(eqA 240 (compA 240 y y) (idA 240)) &&
    eqA 240 (compA 240 y y) negArr

end CFSG.EvenSmallLie.OmegaEight.Weyl
