module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverModelsNative

public section

namespace CFSG.ComponentClassification.J2Cover.Models

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native

@[expose] def oddW3 : List Nat := [1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0]

@[expose] def oddW5 : List Nat := [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

@[expose] def oddWidx : List Nat := [
  0, 1, 4, 11, 18, 23, 32, 37, 40, 46, 48, 57, 62, 70, 80, 81, 83, 85, 86, 88, 93, 94,
  95, 108, 115, 116, 117, 119, 120, 122, 123, 124]

@[expose] def oddC3 : List Nat := [
  0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 62, 0, 0, 0,
  0, 83, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 0, 117, 0, 0, 37, 0, 0, 0,
  0, 0, 46, 0, 122, 0, 0, 0, 0, 0, 0, 0, 0, 23, 0, 0, 0, 0, 93, 0, 0, 0,
  0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 95, 0, 57, 0, 94, 86, 0,
  81, 0, 0, 0, 0, 18, 80, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 0,
  0, 0, 0, 0, 0, 119, 124, 40, 0, 123, 116, 0, 32, 115, 120, 0, 0, 0]

@[expose] def oddC3i : List Nat := [
  0, 1, 0, 0, 4, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 93, 0, 0, 0,
  0, 57, 0, 0, 0, 0, 0, 0, 0, 0, 122, 0, 0, 0, 0, 40, 0, 0, 117, 0, 0, 0,
  0, 0, 46, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 83, 0, 0, 0, 0, 18, 0, 0, 0,
  0, 0, 0, 0, 70, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 88, 0, 23, 0, 80, 86, 0,
  95, 0, 0, 0, 0, 62, 85, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 108, 0,
  0, 0, 0, 0, 0, 123, 120, 37, 0, 115, 124, 0, 48, 119, 116, 0, 0, 0]

@[expose] def oddC5 : List Nat := [
  0, 83, 0, 0, 4, 0, 0, 0, 0, 0, 0, 93, 0, 0, 0, 0, 0, 0, 115, 0, 0, 0,
  0, 122, 0, 0, 0, 0, 0, 0, 0, 0, 62, 0, 0, 0, 0, 11, 0, 0, 23, 0, 0, 0,
  0, 0, 94, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 117, 0, 0, 0,
  0, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 95, 0, 119, 0, 70, 108, 0,
  86, 0, 0, 0, 0, 120, 80, 88, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 81, 0,
  0, 0, 0, 0, 0, 40, 37, 57, 0, 123, 116, 0, 18, 48, 32, 0, 0, 0]

@[expose] def oddC5i : List Nat := [
  0, 48, 0, 0, 4, 0, 0, 0, 0, 0, 0, 37, 0, 0, 0, 0, 0, 0, 122, 0, 0, 0,
  0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 124, 0, 0, 0, 0, 116, 0, 0, 115, 0, 0, 0,
  0, 0, 70, 0, 123, 0, 0, 0, 0, 0, 0, 0, 0, 117, 0, 0, 0, 0, 32, 0, 0, 0,
  0, 0, 0, 0, 85, 0, 0, 0, 0, 0, 0, 0, 0, 0, 94, 108, 0, 1, 0, 80, 88, 0,
  95, 0, 0, 0, 0, 11, 46, 81, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 86, 0,
  0, 0, 0, 0, 0, 18, 120, 62, 0, 83, 93, 0, 23, 119, 57, 0, 0, 0]

@[expose] def oddWidxB (k : Nat) : Bool := oddWidx.contains k

@[expose] def oddCheck (_ : Unit := ()) : Bool :=
  let idt := idA 315
  let g3 := wordArr oddW3
  let g3s := compA 315 g3 g3
  let g5 := wordArr oddW5
  let g5s := compA 315 g5 g5
  let g5i := compA 315 g5s g5s
  let e4 := eltArrs[4]!
  eqA 315 (compA 315 g3 g3s) idt && !(eqA 315 g3 idt) &&
  eqA 315 (compA 315 g5 g5i) idt && !(eqA 315 g5 idt) &&
  eqA 315 (compA 315 g3 e4) (compA 315 e4 g3) && eqA 315 (compA 315 g5 e4) (compA 315 e4 g5) &&
  (allLt 128 fun k => !oddWidxB k ||
    (decide (nth 0 oddC3 k < 128) && oddWidxB (nth 0 oddC3 k) &&
      eqA 315 (compA 315 (compA 315 g3 eltArrs[k]!) g3s) eltArrs[nth 0 oddC3 k]! &&
      decide (nth 0 oddC3i k < 128) && oddWidxB (nth 0 oddC3i k) &&
      eqA 315 (compA 315 (compA 315 g3s eltArrs[k]!) g3) eltArrs[nth 0 oddC3i k]! &&
      decide (nth 0 oddC5 k < 128) && oddWidxB (nth 0 oddC5 k) &&
      eqA 315 (compA 315 (compA 315 g5 eltArrs[k]!) g5i) eltArrs[nth 0 oddC5 k]! &&
      decide (nth 0 oddC5i k < 128) && oddWidxB (nth 0 oddC5i k) &&
      eqA 315 (compA 315 (compA 315 g5i eltArrs[k]!) g5) eltArrs[nth 0 oddC5i k]!)) &&
  (allLt 128 fun i => mulIdx i i != 4 || bitAt fRows i i)

end CFSG.ComponentClassification.J2Cover.Models
