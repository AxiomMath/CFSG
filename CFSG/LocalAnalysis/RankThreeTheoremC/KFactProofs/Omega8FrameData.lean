module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeData
public import Certificates.Data.CFSGNative.Schreier.Enum3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.EvenSmallLie.OmegaEightMinus

@[expose] def betaArrs : Array (Array ℕ) := #[
    #[5, 1, 7, 3, 4, 9, 6, 11, 8, 0, 10, 2, 12, 18, 26, 22, 21, 17, 27, 15, 20, 25, 19, 14, 24,
      16, 23, 13, 28, 36, 44, 40, 32, 38, 46, 42, 45, 31, 47, 35, 37, 30, 39, 34, 41, 29, 43, 33,
      48, 52, 60, 56, 61, 51, 59, 55, 53, 50, 58, 63, 57, 49, 62, 54, 64, 72, 80, 76, 68, 74, 82,
      78, 81, 67, 83, 71, 73, 66, 75, 70, 77, 65, 79, 69, 84, 88, 96, 92, 97, 87, 95, 91, 89, 86,
      94, 99, 93, 85, 98, 90, 100, 108, 116, 112, 104, 110, 118, 114, 117, 103, 119, 107, 109,
      102, 111, 106, 113, 101, 115, 105, 120, 124, 132, 128, 133, 123, 131, 127, 125, 122, 130,
      135, 129, 121, 134, 126],
    #[0, 8, 2, 10, 1, 5, 3, 7, 4, 9, 6, 11, 12, 26, 22, 18, 16, 24, 23, 13, 17, 21, 27, 15, 20,
      25, 19, 14, 28, 44, 40, 36, 32, 46, 42, 38, 41, 29, 43, 33, 45, 31, 47, 35, 37, 30, 39, 34,
      48, 60, 56, 52, 57, 49, 54, 62, 61, 51, 55, 59, 53, 50, 58, 63, 64, 80, 76, 72, 68, 82, 78,
      74, 77, 65, 79, 69, 81, 67, 83, 71, 73, 66, 75, 70, 84, 96, 92, 88, 93, 85, 90, 98, 97, 87,
      91, 95, 89, 86, 94, 99, 100, 116, 112, 108, 104, 118, 114, 110, 113, 101, 115, 105, 117,
      103, 119, 107, 109, 102, 111, 106, 120, 132, 128, 124, 129, 121, 126, 134, 133, 123, 127,
      131, 125, 122, 130, 135],
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
      25, 26, 27, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83,
      84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104,
      105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122,
      123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 28, 29, 30, 31, 32, 33,
      34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56,
      57, 58, 59, 60, 61, 62, 63]]

@[expose] def cArr : Array ℕ :=
    #[4, 64, 6, 68, 28, 1, 32, 3, 100, 8, 104, 10, 12, 55, 94, 134, 20, 84, 62, 127, 48, 17, 130,
      98, 120, 24, 91, 58, 0, 30, 81, 112, 2, 34, 83, 114, 40, 102, 42, 106, 117, 76, 119, 78,
      66, 45, 70, 47, 16, 50, 97, 128, 56, 122, 27, 90, 133, 92, 54, 14, 86, 61, 126, 22, 5, 44,
      65, 109, 7, 46, 69, 111, 37, 116, 39, 118, 101, 73, 105, 75, 80, 29, 82, 33, 21, 60, 85,
      125, 53, 132, 13, 95, 121, 89, 59, 26, 96, 49, 131, 19, 9, 41, 72, 103, 11, 43, 74, 107,
      31, 113, 35, 115, 108, 67, 110, 71, 77, 36, 79, 38, 25, 57, 88, 123, 51, 129, 18, 99, 124,
      87, 63, 23, 93, 52, 135, 15]

@[expose] def tauArr : Array ℕ :=
    #[4, 5, 6, 7, 0, 1, 2, 3, 9, 8, 11, 10, 12, 14, 13, 15, 20, 21, 22, 23, 16, 17, 18, 19, 25,
      24, 26, 27, 28, 30, 29, 31, 32, 34, 33, 35, 40, 41, 42, 43, 36, 37, 38, 39, 44, 45, 46, 47,
      48, 50, 49, 51, 56, 57, 58, 59, 52, 53, 54, 55, 60, 61, 63, 62, 64, 66, 65, 67, 68, 70, 69,
      71, 76, 77, 78, 79, 72, 73, 74, 75, 80, 81, 82, 83, 84, 86, 85, 87, 92, 93, 94, 95, 88, 89,
      90, 91, 96, 97, 99, 98, 100, 102, 101, 103, 104, 106, 105, 107, 112, 113, 114, 115, 108,
      109, 110, 111, 116, 117, 118, 119, 120, 122, 121, 123, 128, 129, 130, 131, 124, 125, 126,
      127, 132, 133, 135, 134]

@[expose] def sArr : Array ℕ :=
    #[0, 1, 16, 17, 4, 9, 20, 25, 8, 5, 24, 21, 12, 18, 14, 19, 2, 3, 13, 15, 6, 11, 22, 26, 10,
      7, 23, 27, 28, 36, 30, 37, 48, 52, 50, 53, 29, 31, 49, 51, 40, 44, 56, 60, 41, 45, 57, 61,
      32, 38, 34, 39, 33, 35, 54, 55, 42, 46, 58, 63, 43, 47, 62, 59, 64, 72, 66, 73, 84, 88, 86,
      89, 65, 67, 85, 87, 76, 80, 92, 96, 77, 81, 93, 97, 68, 74, 70, 75, 69, 71, 90, 91, 78, 82,
      94, 99, 79, 83, 98, 95, 100, 108, 102, 109, 120, 124, 122, 125, 101, 103, 121, 123, 112,
      116, 128, 132, 113, 117, 129, 133, 104, 110, 106, 111, 105, 107, 126, 127, 114, 118, 130,
      135, 115, 119, 134, 131]

@[expose] def nGens : Array (Array ℕ) := #[cArr, tauArr, sArr]

@[expose] def t0S : Array (Array ℕ) := betaArrs.push cArr

@[expose] def frameBase : List (Fin 136) := [0, 4, 28]

@[expose] def j0W : Array (List ℤ) := CFSG.EvenSmallLie.OmegaEight.wordsOf 3 []

@[expose] def t0W : Array (List ℤ) := CFSG.EvenSmallLie.OmegaEight.wordsOf 4 []

@[expose] def j0Levels : Array Level := rawLevels 136 betaArrs (frameBase.map Fin.val).toArray

@[expose] def omegaLevels : Array Level := rawLevels 136 omegaS (omegaBase.map Fin.val).toArray

@[expose] def suppA (t : Array ℕ) : ℕ := (List.range 136).countP fun i => t[i]! != i

@[expose] def conjA (g x : Array ℕ) : Array ℕ := compA 136 (compA 136 g x) (invCand 136 g)

@[expose] def nWordA : List ℕ → Array ℕ
  | [] => idA 136
  | i :: w => compA 136 nGens[i]! (nWordA w)

@[expose] def zArr : Array ℕ := compA 136 (compA 136 betaArrs[0]! betaArrs[1]!) betaArrs[2]!

@[expose] def sixArrs : Array (Array ℕ) :=
  #[betaArrs[0]!, invCand 136 betaArrs[0]!, betaArrs[1]!, invCand 136 betaArrs[1]!,
    betaArrs[2]!, invCand 136 betaArrs[2]!]

@[expose] def notSix (x : Array ℕ) : Bool := allLt 6 fun k => !(eqA 136 x sixArrs[k]!)

@[expose] def candWords : List (List ℕ) :=
  [[]] ++ (List.range 3).map (fun i => [i]) ++
    ((List.range 3).flatMap fun i => (List.range 3).map fun j => [i, j]) ++
    ((List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
      (List.range 3).map fun k => [i, j, k])

@[expose] def samePt (y y' : Array ℕ) : Bool := eqA 136 y y' || eqA 136 y (invCand 136 y')

@[expose] def pickGo (x : Array ℕ) :
    List (List ℕ) → List (Array ℕ) → List (List ℕ) → List (List ℕ)
  | [], _, acc => acc.reverse
  | w :: ws, seen, acc =>
    if acc.length = 4 then acc.reverse else
      let y := conjA (nWordA w) x
      if seen.any (samePt y) then pickGo x ws seen acc else pickGo x ws (y :: seen) (w :: acc)

@[expose] def pick4 (x : Array ℕ) : List (List ℕ) := pickGo x candWords [] []

@[expose] def sepOK (x : Array ℕ) (ws : List (List ℕ)) : Bool :=
  ws.length == 4 && ws.all (fun w => w.all fun i => decide (i < 3)) &&
    allLt 4 fun k => allLt 4 fun l => k == l ||
    (!(eqA 136 (conjA (nWordA ws[k]!) x) (conjA (nWordA ws[l]!) x)) &&
      !(eqA 136 (conjA (nWordA ws[k]!) x) (conjA (nWordA ws[l]!) (invCand 136 x))))

@[expose] def permBits (s : Fin 5 → Fin 5) (u : ℕ) : ℕ :=
  (List.finRange 5).foldl
    (fun acc (i : Fin 5) => if u.testBit (i : ℕ) then acc ^^^ 2 ^ (s i : ℕ) else acc) 0

@[expose] def psiCoord (v : ℕ) : ℕ :=
  (if bNat v 11 then 3 else 0) ^^^ (if bNat v 18 then 6 else 0) ^^^
    (if bNat v 32 then 15 else 0) ^^^ (if bNat v 4 then 23 else 0)

@[expose] def psiIota (u : ℕ) : ℕ :=
  (if (u.testBit 0 ^^ u.testBit 3) ^^ u.testBit 4 then 18 else 0) ^^^
    (if (u.testBit 2 ^^ u.testBit 3) ^^ u.testBit 4 then 11 else 0) ^^^
    (if u.testBit 3 then 4 else 0) ^^^ (if u.testBit 4 then 32 else 0)

@[expose] def psiCode (s : Fin 5 → Fin 5) (v : ℕ) : ℕ :=
  v ^^^ psiIota (psiCoord v) ^^^ psiIota (permBits s (psiCoord v))

@[expose] def psiArr (σ : Equiv.Perm (Fin 5)) : Array ℕ :=
  Array.ofFn (n := 136) fun j => nsIdx[psiCode σ nsArr[j.val]!]!

@[expose] def chainCheck : Bool :=
  rawChainOK 136 (betaArrs.extract 0 3) betaArrs (frameBase.map Fin.val).toArray j0W 4 &&
    rawOrbitSizes 136 betaArrs (frameBase.map Fin.val).toArray == [3, 3, 3] &&
    rawChainOK 136 (t0S.extract 0 4) t0S (frameBase.map Fin.val).toArray t0W 4 &&
    rawOrbitSizes 136 t0S (frameBase.map Fin.val).toArray == [9, 3, 3]

@[expose] def memCheck : Bool :=
  let L := omegaLevels
  let J := j0Levels
  let B := (omegaBase.map Fin.val).toArray
  (allLt 4 fun k => siftA 136 L B 0 t0S[k]!) && siftA 136 L B 0 tauArr &&
    siftA 136 L B 0 sArr && isInvA 136 tauArr (invCand 136 tauArr) &&
    isInvA 136 sArr (invCand 136 sArr) &&
    (allLt 3 fun g => allLt 3 fun i =>
      siftA 136 J (frameBase.map Fin.val).toArray 0 (conjA nGens[g]! betaArrs[i]!)) &&
    eqA 136 (conjA cArr betaArrs[0]!) betaArrs[1]! &&
    eqA 136 (conjA cArr betaArrs[1]!) betaArrs[2]! &&
    (allLt 6 fun k => suppA sixArrs[k]! == 108) &&
    (allLt 6 fun k => allLt 6 fun l => k == l || !(eqA 136 sixArrs[k]! sixArrs[l]!))

@[expose] def eltCheck : Bool :=
  let J := j0Levels
  allLt J[0]!.pts.size fun a => allLt J[1]!.pts.size fun b => allLt J[2]!.pts.size fun c =>
    let x := prod3 136 J a b c
    eqA 136 (compA 136 x (compA 136 x x)) (idA 136) &&
    (allLt J[0]!.pts.size fun a' => allLt J[1]!.pts.size fun b' => allLt J[2]!.pts.size fun c' =>
      eqA 136 (compA 136 x (prod3 136 J a' b' c')) (compA 136 (prod3 136 J a' b' c') x)) &&
    (suppA x == 108) == !(notSix x) &&
    (!(eqA 136 (compA 136 x cArr) (compA 136 cArr x)) || eqA 136 x (idA 136) ||
      eqA 136 x zArr || eqA 136 x (invCand 136 zArr)) &&
    (eqA 136 x (idA 136) || suppA x == 108 || sepOK x (pick4 x))

@[expose] def psiCheck : Bool :=
  let L := omegaLevels
  let B := (omegaBase.map Fin.val).toArray
  decide (∀ σ τ : Equiv.Perm (Fin 5),
      eqA 136 (psiArr (σ * τ)) (compA 136 (psiArr σ) (psiArr τ)) = true) &&
    decide (∀ σ : Equiv.Perm (Fin 5), isInvA 136 (psiArr σ) (invCand 136 (psiArr σ)) = true) &&
    decide (∀ σ : Equiv.Perm (Fin 5),
      eqA 136 (compA 136 (psiArr σ) betaArrs[0]!) (compA 136 betaArrs[0]! (psiArr σ)) = true) &&
    decide (∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → siftA 136 L B 0 (psiArr σ) = true) &&
    !(eqA 136 (psiArr (Equiv.swap 0 1 * Equiv.swap 1 2)) (idA 136))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame
