module

public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Mathieu.Actions
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier

set_option compiler.extract_closed false

@[expose] def permX : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 3, 6, 11, 5] * List.formPerm [2, 8, 4, 10, 7]

@[expose] def permY : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6, 5, 11, 1] * List.formPerm [4, 7, 9, 8, 10]

@[expose] def permZ : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 9] * List.formPerm [1, 7] * List.formPerm [2, 3] * List.formPerm [4, 11] *
    List.formPerm [5, 10] * List.formPerm [6, 8]

@[expose] def wordX : List ℤ :=
  [1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2]

@[expose] def wordY : List ℤ :=
  [-2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1]

@[expose] def wordZ : List ℤ :=
  [1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2,
    1, 2, 1, -2, 1, -2, 1, 2, 1, 2]

@[expose] def fixedDQ : RawSchreierDatum 12 :=
  certificate (by decide) [permX, permY] [[1, 1], [2, 2, 1, 2, 1, 1], [2, 1, 2, 2]] #v[0, 1, 2]
    (by decide)

@[expose] def fourR : Fin 5 → Equiv.Perm (Fin 12) :=
  ![List.formPerm [2, 10] * List.formPerm [3, 5] * List.formPerm [4, 8] * List.formPerm [6, 11],
    List.formPerm [1, 3] * List.formPerm [2, 7] * List.formPerm [5, 6] * List.formPerm [8, 10],
    List.formPerm [1, 5] * List.formPerm [2, 4] * List.formPerm [3, 11] * List.formPerm [7, 10],
    List.formPerm [1, 6] * List.formPerm [4, 10] * List.formPerm [5, 11] * List.formPerm [7, 8],
    List.formPerm [1, 11] * List.formPerm [2, 8] * List.formPerm [3, 6] * List.formPerm [4, 7]]

@[expose] def fourS : Fin 5 → Equiv.Perm (Fin 12) :=
  ![List.formPerm [0, 1] * List.formPerm [4, 8] * List.formPerm [6, 11] * List.formPerm [7, 9],
    List.formPerm [0, 11] * List.formPerm [4, 9] * List.formPerm [5, 6] * List.formPerm [8, 10],
    List.formPerm [0, 6] * List.formPerm [2, 4] * List.formPerm [3, 11] * List.formPerm [8, 9],
    List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11],
    List.formPerm [0, 5] * List.formPerm [2, 8] * List.formPerm [3, 6] * List.formPerm [9, 10]]

@[expose] def fourRWord : Fin 5 → List ℤ :=
  ![[2, 1, 2, 2], [1, 2, 1, 2, 2], [2, 2, 1, 2], [2, 2, 1, 2, 1, 1], [2, 2, 1, 2, 1]]

@[expose] def fourSWord : Fin 5 → List ℤ :=
  ![[2, 1, 2, 1, 1], [1, 2, 1, 1], [2, -1, -1], [1, 2, 1, 2, 1], [2, 2, -1]]

@[expose] def fourList (i : Fin 5) : List (Equiv.Perm (Fin 12)) :=
  [1, fourR i, fourS i, fourR i * fourS i]

@[expose] def memB (g : Equiv.Perm (Fin 12)) (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.any (schreierPermEq g)

@[expose] def conjIndex (g : Equiv.Perm (Fin 12)) (i : Fin 5) : Fin 5 :=
  ((List.finRange 5).find? fun j =>
    memB (g * fourR i * g⁻¹) (fourList j) && memB (g * fourS i * g⁻¹) (fourList j)).getD 0

@[expose] def imageArray (g : Equiv.Perm (Fin 12)) : List ℕ := List.ofFn fun i => (g i : ℕ)

@[expose] def fourGroupArrays : Fin 5 → List (List ℕ) :=
  ![[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 10, 5, 8, 3, 11, 7, 4, 9, 2, 6],
      [1, 0, 2, 3, 8, 5, 11, 9, 4, 7, 10, 6], [1, 0, 10, 5, 4, 3, 6, 9, 8, 7, 2, 11]],
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 3, 7, 1, 4, 6, 5, 2, 10, 9, 8, 11],
      [11, 1, 2, 3, 9, 6, 5, 7, 10, 4, 8, 0], [11, 3, 7, 1, 9, 5, 6, 2, 8, 4, 10, 0]],
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 5, 4, 11, 2, 1, 6, 10, 8, 9, 7, 3],
      [6, 1, 4, 11, 2, 5, 0, 7, 9, 8, 10, 3], [6, 5, 2, 3, 4, 1, 0, 10, 9, 8, 7, 11]],
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 6, 2, 3, 10, 11, 1, 8, 7, 9, 4, 5],
      [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5], [3, 6, 9, 0, 4, 5, 1, 8, 7, 2, 10, 11]],
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 11, 8, 6, 7, 5, 3, 4, 2, 9, 10, 1],
      [5, 1, 8, 6, 4, 0, 3, 7, 2, 10, 9, 11], [5, 11, 2, 3, 7, 0, 6, 4, 8, 10, 9, 1]]]

abbrev permR : Equiv.Perm (Fin 12) := fourR 0

abbrev permS : Equiv.Perm (Fin 12) := fourS 0

@[expose] def checkChainD : Bool := fixedDQ.check && fixedDQ.orderCertificate == 60

@[expose] def checkFour (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all fun g => !schreierPermEq (g ^ 4) 1 || schreierPermEq (g ^ 2) 1

@[expose] def checkInvolutions (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all fun g => !schreierPermEq (g ^ 2) 1 || schreierPermEq g 1 ||
    L.any fun c => schreierPermEq g (c * permR * c⁻¹)

@[expose] def checkConj (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all fun g => (List.finRange 5).all fun i =>
    memB (g * fourR i * g⁻¹) (fourList (conjIndex g i)) &&
      memB (g * fourS i * g⁻¹) (fourList (conjIndex g i))

@[expose] def checkKernel (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all fun g => !(List.finRange 5).all (fun i => conjIndex g i == i) || schreierPermEq g 1

@[expose] def checkPairs (L : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all fun u => L.all fun v =>
    !(schreierPermEq (u ^ 2) 1 && schreierPermEq (v ^ 2) 1 && !schreierPermEq u 1 &&
        !schreierPermEq v 1 && !schreierPermEq u v && schreierPermEq (u * v) (v * u)) ||
      (List.finRange 5).any fun i => memB u (fourList i) && memB v (fourList i)

@[expose] def involutionsOf (L : List (Equiv.Perm (Fin 12))) : List (Equiv.Perm (Fin 12)) :=
  L.filter fun g => schreierPermEq (g ^ 2) 1 && !schreierPermEq g 1

@[expose] def checkCount (L : List (Equiv.Perm (Fin 12))) : Bool :=
  (involutionsOf L).length == 15 && !memB permZ L

@[expose] def checkFourMul : Bool :=
  (List.finRange 5).all fun i => (fourList i).all fun a => (fourList i).all fun b =>
    memB (a * b) (fourList i)

@[expose] def checkFourInv : Bool :=
  (List.finRange 5).all fun i => (fourList i).all fun a => memB a⁻¹ (fourList i)

@[expose] def checkFourAbelian : Bool :=
  (List.finRange 5).all fun i => (fourList i).all fun a =>
    schreierPermEq (a ^ 2) 1 && (fourList i).all fun b => schreierPermEq (a * b) (b * a)

@[expose] def checkFourDistinctEntries : Bool :=
  (List.finRange 5).all fun i => decide (fourList i).Nodup

@[expose] def checkFourSeparated : Bool :=
  (List.finRange 5).all fun i => (List.finRange 5).all fun j =>
    j == i || !(memB (fourR i) (fourList j) && memB (fourS i) (fourList j))

@[expose] def checkFourArrays : Bool :=
  (List.finRange 5).all fun i =>
    ((fourList i).all fun a => (fourGroupArrays i).contains (imageArray a)) &&
      (fourGroupArrays i).all fun arr => (fourList i).any fun a => imageArray a == arr

@[expose] def checkFourWords : Bool :=
  (List.finRange 5).all fun i =>
    schreierPermEq (evalCodes [permX, permY] (fourRWord i)) (fourR i) &&
      schreierPermEq (evalCodes [permX, permY] (fourSWord i)) (fourS i)

@[expose] def checkFourIndex : Bool :=
  (List.finRange 5).all fun i =>
    conjIndex 1 i == i && conjIndex permX i == ![3, 4, 1, 2, 0] i &&
      conjIndex permY i == ![2, 3, 1, 4, 0] i

end CFSG.ComponentClassification.M12Cover
