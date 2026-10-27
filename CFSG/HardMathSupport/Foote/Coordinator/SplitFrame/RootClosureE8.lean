module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley

abbrev rootsL : List (List ℤ) := e8ArtifactRoots

def addL (a b : List ℤ) : List ℤ := List.zipWith (· + ·) a b

def inS (v : List ℤ) : Bool := v.getD 4 0 % 5 == 0

abbrev k4 : Fin Tag.E8.rank := ⟨4, by decide⟩

def S0 : List (List ℤ) := rootsL.filter inS

def walkOK : List ℤ → List ℕ → Option (List ℤ)
  | y, [] => some y
  | y, i :: L =>
    match S0[i]? with
    | none => none
    | some g =>
      if inS y || !(rootsL.contains (addL y g)) then none
      else walkOK (addL y g) L

def runSteps : List (List ℤ) → List (ℕ × ℕ) → Option (List (List ℤ))
  | D, [] => some D
  | D, (i, j) :: L =>
    match D[i]?, D[j]? with
    | some a, some b =>
      if (a != b && rootsL.contains (addL a b)) then runSteps (D ++ [addL a b]) L else none
    | _, _ => none

def tableE8_1 : List (List ℤ × List ℕ) := [
  (([-2, -3, -4, -6, -4, -3, -2, -1] : List ℤ), ([36] : List ℕ)),
  (([-2, -3, -4, -5, -4, -3, -2, -1] : List ℤ), ([13, 36] : List ℕ)),
  (([-2, -3, -3, -5, -4, -3, -2, -1] : List ℤ), ([11, 36] : List ℕ)),
  (([-2, -2, -4, -5, -4, -3, -2, -1] : List ℤ), ([9, 36] : List ℕ)),
  (([-2, -2, -3, -5, -4, -3, -2, -1] : List ℤ), ([8, 36] : List ℕ)),
  (([-2, -2, -3, -4, -4, -3, -2, -1] : List ℤ), ([8, 13, 36] : List ℕ)),
  (([-2, -2, -3, -4, -3, -3, -2, -1] : List ℤ), ([37] : List ℕ)),
  (([-2, -2, -3, -4, -3, -2, -2, -1] : List ℤ), ([36] : List ℕ)),
  (([-2, -2, -3, -4, -3, -2, -1, -1] : List ℤ), ([15, 37] : List ℕ)),
  (([-2, -2, -3, -4, -3, -2, -1, 0] : List ℤ), ([14, 37] : List ℕ)),
  (([-1, -3, -3, -5, -4, -3, -2, -1] : List ℤ), ([5, 36] : List ℕ)),
  (([-1, -2, -3, -5, -4, -3, -2, -1] : List ℤ), ([4, 36] : List ℕ)),
  (([-1, -2, -3, -4, -4, -3, -2, -1] : List ℤ), ([4, 13, 36] : List ℕ)),
  (([-1, -2, -3, -4, -3, -3, -2, -1] : List ℤ), ([7, 37] : List ℕ)),
  (([-1, -2, -3, -4, -3, -2, -2, -1] : List ℤ), ([7, 36] : List ℕ)),
  (([-1, -2, -3, -4, -3, -2, -1, -1] : List ℤ), ([7, 15, 37] : List ℕ)),
  (([-1, -2, -3, -4, -3, -2, -1, 0] : List ℤ), ([7, 14, 37] : List ℕ)),
  (([-1, -2, -2, -4, -4, -3, -2, -1] : List ℤ), ([4, 11, 36] : List ℕ)),
  (([-1, -2, -2, -4, -3, -3, -2, -1] : List ℤ), ([6, 37] : List ℕ)),
  (([-1, -2, -2, -4, -3, -2, -2, -1] : List ℤ), ([6, 36] : List ℕ)),
  (([-1, -2, -2, -4, -3, -2, -1, -1] : List ℤ), ([6, 15, 37] : List ℕ)),
  (([-1, -2, -2, -4, -3, -2, -1, 0] : List ℤ), ([6, 14, 37] : List ℕ)),
  (([-1, -2, -2, -3, -3, -3, -2, -1] : List ℤ), ([5, 37] : List ℕ)),
  (([-1, -2, -2, -3, -3, -2, -2, -1] : List ℤ), ([5, 36] : List ℕ)),
  (([-1, -2, -2, -3, -3, -2, -1, -1] : List ℤ), ([5, 15, 37] : List ℕ)),
  (([-1, -2, -2, -3, -3, -2, -1, 0] : List ℤ), ([5, 14, 37] : List ℕ)),
  (([-1, -2, -2, -3, -2, -2, -2, -1] : List ℤ), ([21, 25, 35] : List ℕ)),
  (([-1, -2, -2, -3, -2, -2, -1, -1] : List ℤ), ([25, 35] : List ℕ)),
  (([-1, -2, -2, -3, -2, -2, -1, 0] : List ℤ), ([24, 35] : List ℕ)),
  (([-1, -2, -2, -3, -2, -1, -1, -1] : List ℤ), ([22, 35] : List ℕ)),
  (([-1, -2, -2, -3, -2, -1, -1, 0] : List ℤ), ([21, 35] : List ℕ)),
  (([-1, -2, -2, -3, -2, -1, 0, 0] : List ℤ), ([35] : List ℕ)),
  (([-1, -1, -2, -3, -3, -3, -2, -1] : List ℤ), ([4, 37] : List ℕ)),
  (([-1, -1, -2, -3, -3, -2, -2, -1] : List ℤ), ([4, 36] : List ℕ)),
  (([-1, -1, -2, -3, -3, -2, -1, -1] : List ℤ), ([4, 15, 37] : List ℕ)),
  (([-1, -1, -2, -3, -3, -2, -1, 0] : List ℤ), ([4, 14, 37] : List ℕ)),
  (([-1, -1, -2, -3, -2, -2, -2, -1] : List ℤ), ([21, 25, 34] : List ℕ)),
  (([-1, -1, -2, -3, -2, -2, -1, -1] : List ℤ), ([25, 34] : List ℕ)),
  (([-1, -1, -2, -3, -2, -2, -1, 0] : List ℤ), ([24, 34] : List ℕ)),
  (([-1, -1, -2, -3, -2, -1, -1, -1] : List ℤ), ([22, 34] : List ℕ)),
  (([-1, -1, -2, -3, -2, -1, -1, 0] : List ℤ), ([21, 34] : List ℕ)),
  (([-1, -1, -2, -3, -2, -1, 0, 0] : List ℤ), ([34] : List ℕ)),
  (([-1, -1, -2, -2, -2, -2, -2, -1] : List ℤ), ([21, 25, 33] : List ℕ)),
  (([-1, -1, -2, -2, -2, -2, -1, -1] : List ℤ), ([25, 33] : List ℕ)),
  (([-1, -1, -2, -2, -2, -2, -1, 0] : List ℤ), ([24, 33] : List ℕ)),
  (([-1, -1, -2, -2, -2, -1, -1, -1] : List ℤ), ([22, 33] : List ℕ)),
  (([-1, -1, -2, -2, -2, -1, -1, 0] : List ℤ), ([21, 33] : List ℕ)),
  (([-1, -1, -2, -2, -2, -1, 0, 0] : List ℤ), ([33] : List ℕ)),
  (([-1, -1, -2, -2, -1, -1, -1, -1] : List ℤ), ([25, 28, 35] : List ℕ)),
  (([-1, -1, -2, -2, -1, -1, -1, 0] : List ℤ), ([24, 28, 35] : List ℕ))
]

def tableE8_2 : List (List ℤ × List ℕ) := [
  (([-1, -1, -2, -2, -1, -1, 0, 0] : List ℤ), ([23, 28, 35] : List ℕ)),
  (([-1, -1, -2, -2, -1, 0, 0, 0] : List ℤ), ([28, 35] : List ℕ)),
  (([-1, -1, -1, -2, -2, -2, -2, -1] : List ℤ), ([21, 25, 32] : List ℕ)),
  (([-1, -1, -1, -2, -2, -2, -1, -1] : List ℤ), ([25, 32] : List ℕ)),
  (([-1, -1, -1, -2, -2, -2, -1, 0] : List ℤ), ([24, 32] : List ℕ)),
  (([-1, -1, -1, -2, -2, -1, -1, -1] : List ℤ), ([22, 32] : List ℕ)),
  (([-1, -1, -1, -2, -2, -1, -1, 0] : List ℤ), ([21, 32] : List ℕ)),
  (([-1, -1, -1, -2, -2, -1, 0, 0] : List ℤ), ([32] : List ℕ)),
  (([-1, -1, -1, -2, -1, -1, -1, -1] : List ℤ), ([25, 26, 35] : List ℕ)),
  (([-1, -1, -1, -2, -1, -1, -1, 0] : List ℤ), ([24, 26, 35] : List ℕ)),
  (([-1, -1, -1, -2, -1, -1, 0, 0] : List ℤ), ([23, 26, 35] : List ℕ)),
  (([-1, -1, -1, -2, -1, 0, 0, 0] : List ℤ), ([26, 35] : List ℕ)),
  (([-1, -1, -1, -1, -1, -1, -1, -1] : List ℤ), ([25, 35] : List ℕ)),
  (([-1, -1, -1, -1, -1, -1, -1, 0] : List ℤ), ([24, 35] : List ℕ)),
  (([-1, -1, -1, -1, -1, -1, 0, 0] : List ℤ), ([23, 35] : List ℕ)),
  (([-1, -1, -1, -1, -1, 0, 0, 0] : List ℤ), ([35] : List ℕ)),
  (([-1, 0, -1, -1, -1, -1, -1, -1] : List ℤ), ([25, 34] : List ℕ)),
  (([-1, 0, -1, -1, -1, -1, -1, 0] : List ℤ), ([24, 34] : List ℕ)),
  (([-1, 0, -1, -1, -1, -1, 0, 0] : List ℤ), ([23, 34] : List ℕ)),
  (([-1, 0, -1, -1, -1, 0, 0, 0] : List ℤ), ([34] : List ℕ)),
  (([0, -1, -1, -2, -2, -2, -2, -1] : List ℤ), ([21, 25] : List ℕ)),
  (([0, -1, -1, -2, -2, -2, -1, -1] : List ℤ), ([25] : List ℕ)),
  (([0, -1, -1, -2, -2, -2, -1, 0] : List ℤ), ([24] : List ℕ)),
  (([0, -1, -1, -2, -2, -1, -1, -1] : List ℤ), ([22] : List ℕ)),
  (([0, -1, -1, -2, -2, -1, -1, 0] : List ℤ), ([21] : List ℕ)),
  (([0, -1, -1, -2, -2, -1, 0, 0] : List ℤ), ([] : List ℕ)),
  (([0, -1, -1, -2, -1, -1, -1, -1] : List ℤ), ([25, 26, 31] : List ℕ)),
  (([0, -1, -1, -2, -1, -1, -1, 0] : List ℤ), ([24, 26, 31] : List ℕ)),
  (([0, -1, -1, -2, -1, -1, 0, 0] : List ℤ), ([23, 26, 31] : List ℕ)),
  (([0, -1, -1, -2, -1, 0, 0, 0] : List ℤ), ([26, 31] : List ℕ)),
  (([0, -1, -1, -1, -1, -1, -1, -1] : List ℤ), ([25, 31] : List ℕ)),
  (([0, -1, -1, -1, -1, -1, -1, 0] : List ℤ), ([24, 31] : List ℕ)),
  (([0, -1, -1, -1, -1, -1, 0, 0] : List ℤ), ([23, 31] : List ℕ)),
  (([0, -1, -1, -1, -1, 0, 0, 0] : List ℤ), ([31] : List ℕ)),
  (([0, -1, 0, -1, -1, -1, -1, -1] : List ℤ), ([25, 30] : List ℕ)),
  (([0, -1, 0, -1, -1, -1, -1, 0] : List ℤ), ([24, 30] : List ℕ)),
  (([0, -1, 0, -1, -1, -1, 0, 0] : List ℤ), ([23, 30] : List ℕ)),
  (([0, -1, 0, -1, -1, 0, 0, 0] : List ℤ), ([30] : List ℕ)),
  (([0, 0, -1, -1, -1, -1, -1, -1] : List ℤ), ([25, 28] : List ℕ)),
  (([0, 0, -1, -1, -1, -1, -1, 0] : List ℤ), ([24, 28] : List ℕ)),
  (([0, 0, -1, -1, -1, -1, 0, 0] : List ℤ), ([23, 28] : List ℕ)),
  (([0, 0, -1, -1, -1, 0, 0, 0] : List ℤ), ([28] : List ℕ)),
  (([0, 0, 0, -1, -1, -1, -1, -1] : List ℤ), ([25, 26] : List ℕ)),
  (([0, 0, 0, -1, -1, -1, -1, 0] : List ℤ), ([24, 26] : List ℕ)),
  (([0, 0, 0, -1, -1, -1, 0, 0] : List ℤ), ([23, 26] : List ℕ)),
  (([0, 0, 0, -1, -1, 0, 0, 0] : List ℤ), ([26] : List ℕ)),
  (([0, 0, 0, 0, -1, -1, -1, -1] : List ℤ), ([25] : List ℕ)),
  (([0, 0, 0, 0, -1, -1, -1, 0] : List ℤ), ([24] : List ℕ)),
  (([0, 0, 0, 0, -1, -1, 0, 0] : List ℤ), ([23] : List ℕ)),
  (([0, 0, 0, 0, -1, 0, 0, 0] : List ℤ), ([] : List ℕ))
]

def tableE8_3 : List (List ℤ × List ℕ) := [
  (([0, 0, 0, 0, 1, 0, 0, 0] : List ℤ), ([] : List ℕ)),
  (([0, 0, 0, 0, 1, 1, 0, 0] : List ℤ), ([16] : List ℕ)),
  (([0, 0, 0, 0, 1, 1, 1, 0] : List ℤ), ([15] : List ℕ)),
  (([0, 0, 0, 0, 1, 1, 1, 1] : List ℤ), ([14] : List ℕ)),
  (([0, 0, 0, 1, 1, 0, 0, 0] : List ℤ), ([13] : List ℕ)),
  (([0, 0, 0, 1, 1, 1, 0, 0] : List ℤ), ([13, 16] : List ℕ)),
  (([0, 0, 0, 1, 1, 1, 1, 0] : List ℤ), ([13, 15] : List ℕ)),
  (([0, 0, 0, 1, 1, 1, 1, 1] : List ℤ), ([13, 14] : List ℕ)),
  (([0, 0, 1, 1, 1, 0, 0, 0] : List ℤ), ([11] : List ℕ)),
  (([0, 0, 1, 1, 1, 1, 0, 0] : List ℤ), ([11, 16] : List ℕ)),
  (([0, 0, 1, 1, 1, 1, 1, 0] : List ℤ), ([11, 15] : List ℕ)),
  (([0, 0, 1, 1, 1, 1, 1, 1] : List ℤ), ([11, 14] : List ℕ)),
  (([0, 1, 0, 1, 1, 0, 0, 0] : List ℤ), ([9] : List ℕ)),
  (([0, 1, 0, 1, 1, 1, 0, 0] : List ℤ), ([9, 16] : List ℕ)),
  (([0, 1, 0, 1, 1, 1, 1, 0] : List ℤ), ([9, 15] : List ℕ)),
  (([0, 1, 0, 1, 1, 1, 1, 1] : List ℤ), ([9, 14] : List ℕ)),
  (([0, 1, 1, 1, 1, 0, 0, 0] : List ℤ), ([8] : List ℕ)),
  (([0, 1, 1, 1, 1, 1, 0, 0] : List ℤ), ([8, 16] : List ℕ)),
  (([0, 1, 1, 1, 1, 1, 1, 0] : List ℤ), ([8, 15] : List ℕ)),
  (([0, 1, 1, 1, 1, 1, 1, 1] : List ℤ), ([8, 14] : List ℕ)),
  (([0, 1, 1, 2, 1, 0, 0, 0] : List ℤ), ([8, 13] : List ℕ)),
  (([0, 1, 1, 2, 1, 1, 0, 0] : List ℤ), ([8, 13, 16] : List ℕ)),
  (([0, 1, 1, 2, 1, 1, 1, 0] : List ℤ), ([8, 13, 15] : List ℕ)),
  (([0, 1, 1, 2, 1, 1, 1, 1] : List ℤ), ([8, 13, 14] : List ℕ)),
  (([0, 1, 1, 2, 2, 1, 0, 0] : List ℤ), ([] : List ℕ)),
  (([0, 1, 1, 2, 2, 1, 1, 0] : List ℤ), ([18] : List ℕ)),
  (([0, 1, 1, 2, 2, 1, 1, 1] : List ℤ), ([17] : List ℕ)),
  (([0, 1, 1, 2, 2, 2, 1, 0] : List ℤ), ([15] : List ℕ)),
  (([0, 1, 1, 2, 2, 2, 1, 1] : List ℤ), ([14] : List ℕ)),
  (([0, 1, 1, 2, 2, 2, 2, 1] : List ℤ), ([14, 18] : List ℕ)),
  (([1, 0, 1, 1, 1, 0, 0, 0] : List ℤ), ([5] : List ℕ)),
  (([1, 0, 1, 1, 1, 1, 0, 0] : List ℤ), ([5, 16] : List ℕ)),
  (([1, 0, 1, 1, 1, 1, 1, 0] : List ℤ), ([5, 15] : List ℕ)),
  (([1, 0, 1, 1, 1, 1, 1, 1] : List ℤ), ([5, 14] : List ℕ)),
  (([1, 1, 1, 1, 1, 0, 0, 0] : List ℤ), ([4] : List ℕ)),
  (([1, 1, 1, 1, 1, 1, 0, 0] : List ℤ), ([4, 16] : List ℕ)),
  (([1, 1, 1, 1, 1, 1, 1, 0] : List ℤ), ([4, 15] : List ℕ)),
  (([1, 1, 1, 1, 1, 1, 1, 1] : List ℤ), ([4, 14] : List ℕ)),
  (([1, 1, 1, 2, 1, 0, 0, 0] : List ℤ), ([4, 13] : List ℕ)),
  (([1, 1, 1, 2, 1, 1, 0, 0] : List ℤ), ([4, 13, 16] : List ℕ)),
  (([1, 1, 1, 2, 1, 1, 1, 0] : List ℤ), ([4, 13, 15] : List ℕ)),
  (([1, 1, 1, 2, 1, 1, 1, 1] : List ℤ), ([4, 13, 14] : List ℕ)),
  (([1, 1, 1, 2, 2, 1, 0, 0] : List ℤ), ([7] : List ℕ)),
  (([1, 1, 1, 2, 2, 1, 1, 0] : List ℤ), ([7, 18] : List ℕ)),
  (([1, 1, 1, 2, 2, 1, 1, 1] : List ℤ), ([7, 17] : List ℕ)),
  (([1, 1, 1, 2, 2, 2, 1, 0] : List ℤ), ([7, 15] : List ℕ)),
  (([1, 1, 1, 2, 2, 2, 1, 1] : List ℤ), ([7, 14] : List ℕ)),
  (([1, 1, 1, 2, 2, 2, 2, 1] : List ℤ), ([7, 14, 18] : List ℕ)),
  (([1, 1, 2, 2, 1, 0, 0, 0] : List ℤ), ([4, 11] : List ℕ)),
  (([1, 1, 2, 2, 1, 1, 0, 0] : List ℤ), ([4, 11, 16] : List ℕ))
]

def tableE8_4 : List (List ℤ × List ℕ) := [
  (([1, 1, 2, 2, 1, 1, 1, 0] : List ℤ), ([4, 11, 15] : List ℕ)),
  (([1, 1, 2, 2, 1, 1, 1, 1] : List ℤ), ([4, 11, 14] : List ℕ)),
  (([1, 1, 2, 2, 2, 1, 0, 0] : List ℤ), ([6] : List ℕ)),
  (([1, 1, 2, 2, 2, 1, 1, 0] : List ℤ), ([6, 18] : List ℕ)),
  (([1, 1, 2, 2, 2, 1, 1, 1] : List ℤ), ([6, 17] : List ℕ)),
  (([1, 1, 2, 2, 2, 2, 1, 0] : List ℤ), ([6, 15] : List ℕ)),
  (([1, 1, 2, 2, 2, 2, 1, 1] : List ℤ), ([6, 14] : List ℕ)),
  (([1, 1, 2, 2, 2, 2, 2, 1] : List ℤ), ([6, 14, 18] : List ℕ)),
  (([1, 1, 2, 3, 2, 1, 0, 0] : List ℤ), ([5] : List ℕ)),
  (([1, 1, 2, 3, 2, 1, 1, 0] : List ℤ), ([5, 18] : List ℕ)),
  (([1, 1, 2, 3, 2, 1, 1, 1] : List ℤ), ([5, 17] : List ℕ)),
  (([1, 1, 2, 3, 2, 2, 1, 0] : List ℤ), ([5, 15] : List ℕ)),
  (([1, 1, 2, 3, 2, 2, 1, 1] : List ℤ), ([5, 14] : List ℕ)),
  (([1, 1, 2, 3, 2, 2, 2, 1] : List ℤ), ([5, 14, 18] : List ℕ)),
  (([1, 1, 2, 3, 3, 2, 1, 0] : List ℤ), ([2, 25, 35] : List ℕ)),
  (([1, 1, 2, 3, 3, 2, 1, 1] : List ℤ), ([2, 24, 35] : List ℕ)),
  (([1, 1, 2, 3, 3, 2, 2, 1] : List ℤ), ([3, 35] : List ℕ)),
  (([1, 1, 2, 3, 3, 3, 2, 1] : List ℤ), ([2, 35] : List ℕ)),
  (([1, 2, 2, 3, 2, 1, 0, 0] : List ℤ), ([4] : List ℕ)),
  (([1, 2, 2, 3, 2, 1, 1, 0] : List ℤ), ([4, 18] : List ℕ)),
  (([1, 2, 2, 3, 2, 1, 1, 1] : List ℤ), ([4, 17] : List ℕ)),
  (([1, 2, 2, 3, 2, 2, 1, 0] : List ℤ), ([4, 15] : List ℕ)),
  (([1, 2, 2, 3, 2, 2, 1, 1] : List ℤ), ([4, 14] : List ℕ)),
  (([1, 2, 2, 3, 2, 2, 2, 1] : List ℤ), ([4, 14, 18] : List ℕ)),
  (([1, 2, 2, 3, 3, 2, 1, 0] : List ℤ), ([2, 25, 34] : List ℕ)),
  (([1, 2, 2, 3, 3, 2, 1, 1] : List ℤ), ([2, 24, 34] : List ℕ)),
  (([1, 2, 2, 3, 3, 2, 2, 1] : List ℤ), ([3, 34] : List ℕ)),
  (([1, 2, 2, 3, 3, 3, 2, 1] : List ℤ), ([2, 34] : List ℕ)),
  (([1, 2, 2, 4, 3, 2, 1, 0] : List ℤ), ([2, 25, 33] : List ℕ)),
  (([1, 2, 2, 4, 3, 2, 1, 1] : List ℤ), ([2, 24, 33] : List ℕ)),
  (([1, 2, 2, 4, 3, 2, 2, 1] : List ℤ), ([3, 33] : List ℕ)),
  (([1, 2, 2, 4, 3, 3, 2, 1] : List ℤ), ([2, 33] : List ℕ)),
  (([1, 2, 2, 4, 4, 3, 2, 1] : List ℤ), ([3, 28, 35] : List ℕ)),
  (([1, 2, 3, 4, 3, 2, 1, 0] : List ℤ), ([2, 25, 32] : List ℕ)),
  (([1, 2, 3, 4, 3, 2, 1, 1] : List ℤ), ([2, 24, 32] : List ℕ)),
  (([1, 2, 3, 4, 3, 2, 2, 1] : List ℤ), ([3, 32] : List ℕ)),
  (([1, 2, 3, 4, 3, 3, 2, 1] : List ℤ), ([2, 32] : List ℕ)),
  (([1, 2, 3, 4, 4, 3, 2, 1] : List ℤ), ([3, 26, 35] : List ℕ)),
  (([1, 2, 3, 5, 4, 3, 2, 1] : List ℤ), ([3, 35] : List ℕ)),
  (([1, 3, 3, 5, 4, 3, 2, 1] : List ℤ), ([3, 34] : List ℕ)),
  (([2, 2, 3, 4, 3, 2, 1, 0] : List ℤ), ([2, 25] : List ℕ)),
  (([2, 2, 3, 4, 3, 2, 1, 1] : List ℤ), ([2, 24] : List ℕ)),
  (([2, 2, 3, 4, 3, 2, 2, 1] : List ℤ), ([3] : List ℕ)),
  (([2, 2, 3, 4, 3, 3, 2, 1] : List ℤ), ([2] : List ℕ)),
  (([2, 2, 3, 4, 4, 3, 2, 1] : List ℤ), ([3, 26, 31] : List ℕ)),
  (([2, 2, 3, 5, 4, 3, 2, 1] : List ℤ), ([3, 31] : List ℕ)),
  (([2, 2, 4, 5, 4, 3, 2, 1] : List ℤ), ([3, 30] : List ℕ)),
  (([2, 3, 3, 5, 4, 3, 2, 1] : List ℤ), ([3, 28] : List ℕ)),
  (([2, 3, 4, 5, 4, 3, 2, 1] : List ℤ), ([3, 26] : List ℕ)),
  (([2, 3, 4, 6, 4, 3, 2, 1] : List ℤ), ([3] : List ℕ))
]

def tableE8 : List (List ℤ × List ℕ) := tableE8_1 ++ tableE8_2 ++ tableE8_3 ++ tableE8_4

def stage2E8_1 : List (ℕ × ℕ) := [(3, 40), (23, 40), (21, 42), (20, 43), (26, 40), (3, 45), (23, 45), (21, 47), (20, 48), (27, 45), (3, 50), (23, 50), (21, 52), (20, 53), (29, 45), (3, 55), (23, 55), (21, 57), (20, 58), (27, 55), (3, 60), (23, 60), (21, 62), (20, 63), (26, 60), (3, 65), (23, 65), (21, 67), (20, 68), (32, 50), (3, 70), (23, 70), (21, 72), (20, 73), (29, 70), (3, 75), (23, 75), (21, 77), (20, 78), (26, 75), (3, 80), (23, 80), (21, 82), (20, 83), (27, 80), (3, 85), (23, 85), (21, 87), (20, 88), (40, 66), (23, 90), (21, 91), (20, 92), (32, 90), (23, 94), (21, 95), (20, 96), (27, 94), (23, 98), (21, 99), (20, 100), (26, 98), (23, 102), (21, 103), (20, 104), (29, 102), (23, 106), (21, 107), (20, 108), (36, 91), (21, 110), (20, 111), (23, 111), (20, 113), (21, 114), (32, 110), (21, 116), (20, 117), (23, 117), (20, 119), (21, 120), (27, 116), (21, 122), (20, 123), (23, 123), (20, 125), (21, 126), (26, 122), (21, 128), (20, 129), (23, 129), (20, 131), (21, 132), (29, 128), (21, 134), (20, 135), (23, 135), (20, 137), (21, 138), (40, 103), (21, 140), (20, 141), (23, 141), (20, 143), (21, 144), (29, 140), (21, 146), (20, 147), (23, 147), (20, 149), (21, 150), (26, 146), (21, 152), (20, 153), (23, 153), (20, 155), (21, 156), (27, 152), (21, 158), (20, 159), (23, 159), (20, 161), (21, 162), (32, 158), (21, 164), (20, 165), (23, 165), (20, 167), (21, 168), (36, 143), (20, 170), (21, 171), (23, 172), (29, 170), (20, 174), (21, 175), (23, 176), (26, 174), (20, 178), (21, 179), (23, 180), (27, 178), (20, 182), (21, 183), (23, 184), (32, 182), (20, 186), (21, 187), (23, 188), (40, 155), (20, 190), (21, 191), (23, 192), (27, 190), (20, 194), (21, 195), (23, 196), (26, 194), (20, 198), (21, 199), (23, 200), (29, 198), (20, 202), (21, 203), (23, 204), (32, 194), (20, 206), (21, 207), (23, 208), (26, 206), (20, 210), (21, 211), (23, 212), (27, 210), (20, 214), (21, 215), (23, 216), (29, 210), (20, 218), (21, 219), (23, 220), (27, 218), (20, 222), (21, 223), (23, 224), (26, 222), (20, 226), (21, 227), (23, 228), (36, 193), (27, 230), (26, 231), (29, 232), (32, 231), (26, 234), (27, 235), (29, 235), (27, 237), (26, 238)]
def stage2E8_2 : List (ℕ × ℕ) := [(2, 40), (3, 40), (21, 40), (3, 43), (20, 43), (3, 45), (23, 43), (20, 47), (21, 48), (32, 40), (2, 50), (3, 50), (21, 50), (3, 53), (20, 53), (3, 55), (23, 53), (20, 57), (21, 58), (27, 50), (2, 60), (3, 60), (21, 60), (3, 63), (20, 63), (3, 65), (23, 63), (20, 67), (21, 68), (26, 60), (2, 70), (3, 70), (21, 70), (3, 73), (20, 73), (3, 75), (23, 73), (20, 77), (21, 78), (29, 70), (2, 80), (3, 80), (21, 80), (3, 83), (20, 83), (3, 85), (23, 83), (20, 87), (21, 88), (40, 54), (20, 90), (21, 91), (23, 92), (27, 90), (20, 94), (21, 95), (23, 96), (26, 94), (20, 98), (21, 99), (23, 100), (29, 98), (20, 102), (21, 103), (23, 104), (32, 94), (20, 106), (21, 107), (23, 108), (26, 106), (20, 110), (21, 111), (23, 112), (27, 110), (20, 114), (21, 115), (23, 116), (29, 110), (20, 118), (21, 119), (23, 120), (27, 118), (20, 122), (21, 123), (23, 124), (26, 122), (20, 126), (21, 127), (23, 128), (36, 93), (27, 130), (26, 131), (29, 132), (32, 131), (26, 134), (27, 135), (29, 135), (27, 137), (26, 138), (40, 108), (3, 140), (23, 140), (21, 142), (20, 143), (26, 140), (3, 145), (23, 145), (21, 147), (20, 148), (27, 145), (3, 150), (23, 150), (21, 152), (20, 153), (29, 145), (3, 155), (23, 155), (21, 157), (20, 158), (27, 155), (3, 160), (23, 160), (21, 162), (20, 163), (26, 160), (3, 165), (23, 165), (21, 167), (20, 168), (32, 150), (3, 170), (23, 170), (21, 172), (20, 173), (29, 170), (3, 175), (23, 175), (21, 177), (20, 178), (26, 175), (3, 180), (23, 180), (21, 182), (20, 183), (27, 180), (3, 185), (23, 185), (21, 187), (20, 188), (40, 171), (21, 190), (20, 191), (23, 191), (20, 193), (21, 194), (29, 190), (21, 196), (20, 197), (23, 197), (20, 199), (21, 200), (26, 196), (21, 202), (20, 203), (23, 203), (20, 205), (21, 206), (27, 202), (21, 208), (20, 209), (23, 209), (20, 211), (21, 212), (32, 208), (21, 214), (20, 215), (23, 215), (20, 217), (21, 218), (36, 193), (20, 220), (21, 221), (23, 222), (29, 220), (20, 224), (21, 225), (23, 226), (26, 224), (20, 228), (21, 229), (23, 230), (27, 228), (20, 232), (21, 233), (23, 234), (32, 232), (20, 236), (21, 237), (23, 238)]
def stage2E8_3 : List (ℕ × ℕ) := [(4, 40), (5, 40), (6, 40), (7, 40), (14, 40), (4, 45), (5, 45), (6, 45), (7, 45), (15, 40), (4, 50), (5, 50), (6, 50), (7, 50), (17, 40), (4, 55), (5, 55), (6, 55), (7, 55), (15, 55), (4, 60), (5, 60), (6, 60), (7, 60), (18, 40), (4, 65), (5, 65), (6, 65), (7, 65), (36, 40), (4, 70), (5, 70), (6, 70), (7, 70), (17, 70), (4, 75), (5, 75), (6, 75), (7, 75), (18, 70), (4, 80), (5, 80), (6, 80), (7, 80), (23, 70), (4, 85), (5, 85), (6, 85), (7, 85), (40, 61), (5, 90), (6, 90), (7, 90), (29, 90), (6, 94), (7, 94), (26, 94), (7, 97), (27, 97), (36, 90), (5, 100), (6, 100), (7, 100), (23, 100), (5, 104), (6, 104), (7, 104), (21, 104), (5, 108), (6, 108), (7, 108), (20, 108), (5, 112), (6, 112), (7, 112), (29, 100), (6, 116), (7, 116), (23, 116), (6, 119), (7, 119), (21, 119), (6, 122), (7, 122), (20, 122), (6, 125), (7, 125), (26, 116), (7, 128), (23, 128), (7, 130), (21, 130), (7, 132), (20, 132), (7, 134), (27, 128), (23, 136), (21, 137), (20, 138), (40, 101), (6, 140), (7, 140), (17, 140), (6, 143), (7, 143), (18, 140), (6, 146), (7, 146), (23, 140), (6, 149), (7, 149), (26, 140), (7, 152), (17, 152), (7, 154), (18, 152), (7, 156), (23, 152), (7, 158), (27, 152), (17, 160), (18, 160), (23, 160), (29, 152), (7, 164), (17, 164), (7, 166), (18, 164), (7, 168), (23, 164), (7, 170), (27, 164), (17, 172), (18, 172), (23, 172), (26, 172), (17, 176), (18, 176), (23, 176), (36, 149), (6, 180), (7, 180), (26, 180), (7, 183), (27, 183), (29, 183), (7, 186), (27, 186), (26, 188), (40, 144), (7, 190), (15, 190), (7, 192), (18, 190), (7, 194), (20, 190), (7, 196), (27, 190), (15, 198), (18, 198), (20, 198), (26, 198), (15, 202), (18, 202), (20, 202), (29, 202), (15, 206), (18, 206), (20, 206), (36, 190), (7, 210), (18, 210), (7, 212), (20, 210), (7, 214), (23, 210), (7, 216), (20, 216), (7, 218), (21, 218), (7, 220), (27, 210), (18, 222), (20, 222), (23, 222), (20, 225), (21, 226), (26, 222), (18, 228), (20, 228), (23, 228), (20, 231), (21, 232), (29, 228), (18, 234), (20, 234), (23, 234), (20, 237), (21, 238)]
def stage2E8_4 : List (ℕ × ℕ) := [(4, 40), (5, 40), (8, 40), (5, 43), (9, 40), (5, 45), (11, 40), (9, 47), (13, 40), (14, 40), (4, 50), (5, 50), (8, 50), (5, 53), (9, 50), (5, 55), (11, 50), (9, 57), (13, 50), (15, 40), (4, 60), (5, 60), (8, 60), (5, 63), (9, 60), (5, 65), (11, 60), (9, 67), (13, 60), (16, 40), (4, 70), (5, 70), (8, 70), (5, 73), (9, 70), (5, 75), (11, 70), (9, 77), (13, 70), (36, 40), (4, 80), (5, 80), (8, 80), (5, 83), (9, 80), (5, 85), (11, 80), (9, 87), (13, 80), (40, 54), (9, 90), (13, 90), (15, 90), (9, 93), (13, 93), (16, 90), (9, 96), (13, 96), (20, 90), (9, 99), (13, 99), (16, 99), (9, 102), (13, 102), (21, 99), (9, 105), (13, 105), (27, 90), (15, 108), (16, 108), (20, 108), (16, 111), (21, 111), (32, 108), (15, 114), (16, 114), (20, 114), (16, 117), (21, 117), (36, 90), (9, 120), (13, 120), (20, 120), (9, 123), (13, 123), (21, 123), (9, 126), (13, 126), (23, 126), (9, 129), (13, 129), (27, 120), (20, 132), (21, 133), (23, 134), (32, 132), (20, 136), (21, 137), (23, 138), (40, 94), (5, 140), (11, 140), (13, 140), (16, 140), (5, 144), (11, 144), (13, 144), (21, 140), (5, 148), (11, 148), (13, 148), (20, 148), (5, 152), (11, 152), (13, 152), (29, 140), (16, 156), (21, 156), (20, 158), (36, 140), (5, 160), (11, 160), (13, 160), (21, 160), (5, 164), (11, 164), (13, 164), (20, 164), (5, 168), (11, 168), (13, 168), (23, 164), (5, 172), (11, 172), (13, 172), (20, 172), (5, 176), (11, 176), (13, 176), (21, 176), (5, 180), (11, 180), (13, 180), (29, 160), (21, 184), (20, 185), (23, 185), (20, 187), (21, 188), (40, 145), (8, 190), (9, 190), (11, 190), (9, 193), (13, 190), (32, 190), (9, 196), (13, 196), (27, 196), (36, 190), (8, 200), (9, 200), (11, 200), (9, 203), (13, 200), (23, 200), (8, 206), (9, 206), (11, 206), (9, 209), (13, 206), (21, 206), (8, 212), (9, 212), (11, 212), (9, 215), (13, 212), (20, 212), (8, 218), (9, 218), (11, 218), (9, 221), (13, 218), (32, 200), (9, 224), (13, 224), (23, 224), (9, 227), (13, 227), (21, 227), (9, 230), (13, 230), (20, 230), (9, 233), (13, 233), (27, 224), (23, 236), (21, 237), (20, 238)]
def repsE8 : List (List ℤ) := [[0, 0, 0, 0, 1, 0, 0, 0], [0, 1, 1, 2, 2, 1, 0, 0], [0, -1, -1, -2, -2, -1, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0]]


def coverOK (r : List ℤ) (L : List (ℕ × ℕ)) : Bool :=
  match runSteps (S0 ++ [r]) L with
  | some D => rootsL.all fun x => D.contains x
  | none => false

def targetOf (x : List ℤ) : Option (List ℤ) :=
  match tableE8.find? (fun p => p.1 == x) with
  | some (_, moves) => walkOK x moves
  | none => none

def tableOK : Bool :=
  (rootsL.filter fun x => !inS x).all fun x =>
    match targetOf x with
    | some r => repsE8.contains r
    | none => false

theorem tableOK_eq : tableOK = true := by decide +kernel

theorem cover_1 : coverOK [0, 0, 0, 0, 1, 0, 0, 0] stage2E8_1 = true := by decide +kernel
theorem cover_2 : coverOK [0, 1, 1, 2, 2, 1, 0, 0] stage2E8_2 = true := by decide +kernel
theorem cover_3 : coverOK [0, -1, -1, -2, -2, -1, 0, 0] stage2E8_3 = true := by decide +kernel
theorem cover_4 : coverOK [0, 0, 0, 0, -1, 0, 0, 0] stage2E8_4 = true := by decide +kernel

theorem mem_of_contains {l : List ℤ} {L : List (List ℤ)} (h : L.contains l = true) : l ∈ L := by
  simpa using h

theorem exists_ofFn_of_length {α : Type} (l : List α) (n : ℕ) (h : l.length = n) :
    ∃ v : Fin n → α, List.ofFn v = l := by
  subst h
  exact ⟨l.get, List.ofFn_get l⟩

theorem ofFn_addL (v w : Fin Tag.E8.rank → ℤ) :
    addL (List.ofFn v) (List.ofFn w) = List.ofFn (v + w) := by
  apply List.ext_getElem
  · simp [addL]
  · intro n h1 h2
    simp [addL]

theorem inS_ofFn (v : Fin Tag.E8.rank → ℤ) :
    inS (List.ofFn v) = true ↔ (5 : ℤ) ∣ v k4 := by
  have hlt : 4 < Tag.E8.rank := by decide
  have h4 : (List.ofFn v).getD 4 0 = v k4 := by
    simp [List.getD_eq_getElem?_getD, hlt, k4]
  simp only [inS, h4, beq_iff_eq]
  omega

theorem mem_S0_iff (l : List ℤ) : l ∈ S0 ↔ l ∈ rootsL ∧ inS l = true := by
  simp [S0, List.mem_filter]

theorem inS_of_mem_S0 {l : List ℤ} (h : l ∈ S0) : inS l = true :=
  ((mem_S0_iff l).1 h).2

section Certs113

theorem mem_rootsL_of_isRoot {v : Fin Tag.E8.rank → ℤ} (hv : IsRoot Tag.E8 v) :
    List.ofFn v ∈ rootsL :=
  (e8_root_certificate.1 v).1 hv

theorem isRoot_of_mem_rootsL {v : Fin Tag.E8.rank → ℤ} (hv : List.ofFn v ∈ rootsL) :
    IsRoot Tag.E8 v :=
  (e8_root_certificate.1 v).2 hv

theorem ne_zero_of_isRoot {v : Fin Tag.E8.rank → ℤ} (hv : IsRoot Tag.E8 v) : v ≠ 0 :=
  (e8_root_certificate.2.2.2.2.1 v hv).1

theorem pinnedX_mem_rootSubgroup {K : Type} [Field K] (α : Fin Tag.E8.rank → ℤ) (c : K) :
    pinnedX Tag.E8 K α c ∈ rootSubgroup Tag.E8 K α := by
  unfold rootSubgroup
  exact Subgroup.subset_closure ⟨c, rfl⟩

def PL (K : Type) [Field K] (H : Subgroup (ModGL Tag.E8 K)) (l : List ℤ) : Prop :=
  ∃ v : Fin Tag.E8.rank → ℤ, List.ofFn v = l ∧ IsRoot Tag.E8 v ∧ rootSubgroup Tag.E8 K v ≤ H

theorem PL_of_S0 {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (hX : rootSpan Tag.E8 K (cosetRoots Tag.E8 k4 5) ≤ H) {l : List ℤ} (hl : l ∈ S0) :
    PL K H l := by
  obtain ⟨hmem, hin⟩ := (mem_S0_iff l).1 hl
  obtain ⟨v, rfl⟩ := exists_ofFn_of_length l Tag.E8.rank (e8_root_certificate.2.1 l hmem)
  have hroot : IsRoot Tag.E8 v := isRoot_of_mem_rootsL hmem
  have h5 : (5 : ℤ) ∣ v k4 := (inS_ofFn v).1 hin
  have hmemS : v ∈ cosetRoots Tag.E8 k4 5 := ⟨hroot, by exact_mod_cast h5⟩
  exact ⟨v, rfl, hroot, (le_biSup (rootSubgroup Tag.E8 K) hmemS).trans hX⟩

end Certs113

section CertsAll


theorem rootSubgroup_add_le {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    {v w : Fin Tag.E8.rank → ℤ} (hv : IsRoot Tag.E8 v) (hw : IsRoot Tag.E8 w)
    (hvw : IsRoot Tag.E8 (v + w)) (hne : v ≠ w)
    (hA : rootSubgroup Tag.E8 K v ≤ H) (hB : rootSubgroup Tag.E8 K w ≤ H) :
    rootSubgroup Tag.E8 K (v + w) ≤ H := by
  have hv0 : v ≠ -w := by
    intro h
    apply ne_zero_of_isRoot hvw
    rw [h, neg_add_cancel]
  obtain ⟨h1, -⟩ := CFSG.LieType.Chevalley.simply_laced_root_commutator_unit Tag.E8
    (Or.inr (Or.inr (Or.inr rfl))) hv hw hne hv0
  obtain ⟨hC, hcomm⟩ := h1 hvw
  have hpin : ∀ c : K, pinnedX Tag.E8 K (v + w) c ∈ H := by
    intro c
    rcases hC with h | h
    · have h2 := hcomm K 1 c
      have key : ((1 : ℤ) : K) * 1 * c = c := by simp
      rw [h, key] at h2
      rw [← h2, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hA (pinnedX_mem_rootSubgroup v 1))
        (hB (pinnedX_mem_rootSubgroup w c))) (H.inv_mem (hA (pinnedX_mem_rootSubgroup v 1))))
        (H.inv_mem (hB (pinnedX_mem_rootSubgroup w c)))
    · have h2 := hcomm K 1 (-c)
      have key : ((-1 : ℤ) : K) * 1 * (-c) = c := by simp
      rw [h, key] at h2
      rw [← h2, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem (hA (pinnedX_mem_rootSubgroup v 1))
        (hB (pinnedX_mem_rootSubgroup w (-c)))) (H.inv_mem (hA (pinnedX_mem_rootSubgroup v 1))))
        (H.inv_mem (hB (pinnedX_mem_rootSubgroup w (-c))))
  unfold rootSubgroup
  rw [Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  exact hpin c

theorem walkOK_sound {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (hS : ∀ l ∈ S0, PL K H l) (L : List ℕ) :
    ∀ (y z : List ℤ), PL K H y → walkOK y L = some z → PL K H z := by
  induction L with
  | nil =>
    intro y z hy h
    simp only [walkOK, Option.some.injEq] at h
    subst h
    exact hy
  | cons i L ih =>
    intro y z hy h
    simp only [walkOK] at h
    split at h
    · simp at h
    · rename_i g hg
      have hgS : g ∈ S0 := List.mem_of_getElem? hg
      obtain ⟨v, rfl, hv, hA⟩ := hy
      obtain ⟨w, rfl, hw, hB⟩ := hS g hgS
      split_ifs at h with hbad
      · have hyS : inS (List.ofFn v) = false ∧ rootsL.contains (addL (List.ofFn v) (List.ofFn w)) = true := by
          cases h1 : inS (List.ofFn v) <;> cases h2 : rootsL.contains (addL (List.ofFn v) (List.ofFn w)) <;> simp_all
        have hm : addL (List.ofFn v) (List.ofFn w) ∈ rootsL := mem_of_contains hyS.2
        rw [ofFn_addL] at hm
        have hvw : IsRoot Tag.E8 (v + w) := isRoot_of_mem_rootsL hm
        have hne : v ≠ w := by
          rintro rfl
          have h2 := inS_of_mem_S0 hgS
          simp_all
        have hsub : rootSubgroup Tag.E8 K (v + w) ≤ H :=
          rootSubgroup_add_le H hv hw hvw hne hA hB
        exact ih _ z ⟨v + w, (ofFn_addL v w).symm, hvw, hsub⟩ h

theorem runSteps_sound {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (L : List (ℕ × ℕ)) :
    ∀ (D D' : List (List ℤ)), (∀ x ∈ D, PL K H x) →
      runSteps D L = some D' → ∀ x ∈ D', PL K H x := by
  induction L with
  | nil =>
    intro D D' hD h
    simp only [runSteps, Option.some.injEq] at h
    subst h
    exact hD
  | cons p L ih =>
    obtain ⟨i, j⟩ := p
    intro D D' hD h
    simp only [runSteps] at h
    split at h
    · rename_i a b ha hb
      split_ifs at h with hc
      · have hc' := hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc'
        have hnew : ∀ x ∈ D ++ [addL a b], PL K H x := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hD x hx
          · rw [List.mem_singleton] at hx
            subst hx
            obtain ⟨va, rfl, hva, hA⟩ := hD a (List.mem_of_getElem? ha)
            obtain ⟨vb, rfl, hvb, hB⟩ := hD b (List.mem_of_getElem? hb)
            have hne : va ≠ vb := fun e => hc'.1 (by rw [e])
            have hm : addL (List.ofFn va) (List.ofFn vb) ∈ rootsL := mem_of_contains hc'.2
            rw [ofFn_addL] at hm
            have hvw := isRoot_of_mem_rootsL hm
            exact ⟨va + vb, (ofFn_addL va vb).symm, hvw,
              rootSubgroup_add_le H hva hvb hvw hne hA hB⟩
        exact ih _ _ hnew h
    · simp at h

theorem cover_sound {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (hS : ∀ l ∈ S0, PL K H l) (r : List ℤ) (L : List (ℕ × ℕ)) (hr : PL K H r)
    (hc : coverOK r L = true) : ∀ x ∈ rootsL, PL K H x := by
  unfold coverOK at hc
  split at hc
  · rename_i D hD
    have hdom : ∀ x ∈ S0 ++ [r], PL K H x := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hS x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        exact hr
    have hall := runSteps_sound H L (S0 ++ [r]) D hdom hD
    intro x hx
    exact hall x (mem_of_contains (List.all_eq_true.1 hc x hx))
  · simp at hc

theorem targetOf_sound {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (hS : ∀ l ∈ S0, PL K H l) {β r : List ℤ} (hPL : PL K H β) (h : targetOf β = some r) :
    PL K H r := by
  unfold targetOf at h
  split at h
  · exact walkOK_sound H hS _ β r hPL h
  · simp at h

theorem all_PL {K : Type} [Field K] (H : Subgroup (ModGL Tag.E8 K))
    (hS : ∀ l ∈ S0, PL K H l) {β : List ℤ} (hβ : β ∈ rootsL) (hβS : inS β = false)
    (hPL : PL K H β) : ∀ x ∈ rootsL, PL K H x := by
  have hmem : β ∈ rootsL.filter fun x => !inS x := by
    rw [List.mem_filter]
    exact ⟨hβ, by simp [hβS]⟩
  have h := List.all_eq_true.1 tableOK_eq β hmem
  obtain ⟨r, hr⟩ : ∃ r, targetOf β = some r := by
    cases hT : targetOf β with
    | none => simp [hT] at h
    | some r => exact ⟨r, rfl⟩
  simp only [hr] at h
  have hrR : r ∈ repsE8 := mem_of_contains h
  have hPr := targetOf_sound H hS hPL hr
  simp only [repsE8, List.mem_cons, List.mem_nil_iff, or_false] at hrR
  rcases hrR with rfl | rfl | rfl | rfl
  · exact cover_sound H hS _ _ hPr cover_1
  · exact cover_sound H hS _ _ hPr cover_2
  · exact cover_sound H hS _ _ hPr cover_3
  · exact cover_sound H hS _ _ hPr cover_4

theorem eq_top_of_rootSubgroup_le_E8 {K : Type} [Field K]
    (H : Subgroup (ModGL Tag.E8 K)) (hH : H ≤ adjointGroup Tag.E8 K)
    (hX : rootSpan Tag.E8 K (cosetRoots Tag.E8 k4 5) ≤ H)
    {β : Fin Tag.E8.rank → ℤ} (hβ : IsRoot Tag.E8 β) (hβS : β ∉ cosetRoots Tag.E8 k4 5)
    (hU : rootSubgroup Tag.E8 K β ≤ H) : H = adjointGroup Tag.E8 K := by
  have hS : ∀ l ∈ S0, PL K H l := fun l hl => PL_of_S0 H hX hl
  have hβin : inS (List.ofFn β) = false := by
    cases h : inS (List.ofFn β)
    · rfl
    · exact absurd ((inS_ofFn β).1 h) (fun hd => hβS ⟨hβ, by exact_mod_cast hd⟩)
  have hall := all_PL H hS (mem_rootsL_of_isRoot hβ) hβin ⟨β, rfl, hβ, hU⟩
  refine le_antisymm hH ?_
  rw [adjointGroup_eq_rootSpan]
  refine iSup₂_le fun v hv => ?_
  obtain ⟨u, hu, -, hsub⟩ := hall (List.ofFn v) (mem_rootsL_of_isRoot (show IsRoot Tag.E8 v from hv))
  have huv : u = v := List.ofFn_injective hu
  subst huv
  exact hsub

end CertsAll

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

end
