module

public import CFSG.Sporadic.Schreier.RuArrays
public import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import CFSG.Sporadic.Schreier.RuEnum
public import CFSG.Sporadic.Schreier.RuEnum
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.EvenSporadicStandard.Induction.TMemRu

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.RuSchreier CFSG.PSL3Four.Native

@[expose] def tmWordA : List ℤ :=
  [2, 2, 2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, 2, 2, -1, -2, -1, -2, -2,
  -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2,
  -1, -2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1,
  2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, -2, 1, -2,
  1, -2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1,
  1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1,
  2, 2, 1, 1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, -1]

@[expose] def tmWordB : List ℤ :=
  [1, -2, 1, -2, 1, -2, 1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2,
  -1, 2, -1, 2, -1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2,
  -1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2,
  -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -2, 1, -2, 1, -2, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, -1,
  2, -1, -2, -1, -2, -2, -1, 2, -1]

@[expose] def tmWordZ : List ℤ :=
  [1, 2, -1, -2, -1, -2, -1, -1, 2, -1, 2, 2, -1, -2, -1, 2, 1, 1, 2, 2, 1, 1, -2, -1, -1, 2, -1,
  -2, 1, 2]

@[expose] def tmWordL : List ℤ :=
  [-1, -2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, -2, -2, 1, -2, 1, -2, 1, -2, 1, 2,
  -1, 2, -1, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2,
  -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 1, 1, 2, 1,
  2, 1, 2, 2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2,
  -1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 2, -1, 2, -1, -2, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -2, -1,
  -2, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, -1,
  -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, -1, 2, -1, -2, -1, -2, -1, -2, -2,
  -1, 2, -1, -2, -2, -1, -2]

@[expose] def tmWordG0 : List ℤ :=
  [-4, 3, 3, 2, 1, 4, 3, 4, 1, -4, -1, 2, -3, -3, -4, 2, 4, 4, 2, -4, -2, 1, 4, 1, 3, 1, 1, 1, 2,
  1, -2, 1, 2, 2, 1, 1, 2, -1, 2, 2]

@[expose] def tmWordG1 : List ℤ :=
  [4, -3, 2, 1, -3, 2, 3, 3, -2, 1, -3, -3, -4, -2, -3, 2, 1, 2, -4, -4, -3, 1, 1, -4, 2]

@[expose] def tmWordsS : List (List ℤ) :=
  [
    [2, 2, 2, 1, 2, 1, 2, -1, 2, 1, -2, -2, 1, -2, -1, -2, -2, -2, -1, -1],
    [1, 2, -1, -1, -2, -2, -1, -1, -2, -2, -2, -1, 2, -1],
    [-2, -2, -1, -2, -1, -1, -2, 1, 2],
    [-1, -2, -1, 2, -1, 2, 2, -1, -2]]

@[expose] def tmWordsC : List (List ℤ) :=
  [
    [],
    [-2, -1, -1, 2, -1, -2, -2, -1, 2, -1, 2, 2, -1, -2, -1, 2, 1, 1, 2, 2, 1, 1, -2, -1],
    [-2, -1, -1, -2, -1, 2, -1, -2, -1, 2, -1, 2, 2, -1, -2, -1, 2, -1, -2, 1, 2],
    [1, -2, -2, -1, 2, 2, 1, 2, 2, 1, 1, 2, 1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, 2],
    [2, 2, 2, 1, 2, 1, 2, -1, 2, 1, -2, -2, 1, 1, -2, -2, 1, -2],
    [1, -2, -1, -2, 1, 2, -1],
    [1, 1, -2, -2, 1, 2, 1, 2, 2, 1, 1, 2, 1, -2, -1, -2, -1, 2]]

@[expose] def tmZFix : ℕ := 0

@[expose] def tmGen2 : Array (Array ℕ) := #[ruA0A, ruA1A]

@[expose] def tmGen2i : Array (Array ℕ) := #[ruInv ruA0A, ruInv ruA1A]

@[expose, irreducible] def tmTA : Array ℕ := wordA 4060 tmGen2 tmGen2i tmWordA

@[expose, irreducible] def tmTB : Array ℕ := wordA 4060 tmGen2 tmGen2i tmWordB

@[expose] def tmGenAB : Array (Array ℕ) := #[tmTA, tmTB]

@[expose] def tmGenABi : Array (Array ℕ) := #[ruInv tmTA, ruInv tmTB]

@[expose, irreducible] def tmTZ : Array ℕ := wordA 4060 tmGenAB tmGenABi tmWordZ

@[expose, irreducible] def tmTL : Array ℕ := wordA 4060 tmGen2 tmGen2i tmWordL

@[expose, irreducible] def tmTAl : Array ℕ := compA 4060 (compA 4060 tmTL tmTA) (ruInv tmTL)

@[expose, irreducible] def tmTBl : Array ℕ := compA 4060 (compA 4060 tmTL tmTB) (ruInv tmTL)

@[expose] def tmGen4 : Array (Array ℕ) := #[tmTA, tmTB, tmTAl, tmTBl]

@[expose] def tmGen4i : Array (Array ℕ) := #[ruInv tmTA, ruInv tmTB, ruInv tmTAl, ruInv tmTBl]

@[expose, irreducible] def tmSGen (i : ℕ) : Array ℕ :=
  wordA 4060 tmGenAB tmGenABi (tmWordsS.getD i [])

@[expose] def tmSTabs : Array (Array ℕ) := #[tmSGen 0, tmSGen 1, tmSGen 2, tmSGen 3]

@[expose, irreducible] def tmSEnum : Enum := enumBFS 4060 tmSTabs 64

@[expose, irreducible] def tmCGen (j : ℕ) : Array ℕ :=
  wordA 4060 tmGenAB tmGenABi (tmWordsC.getD j [])

@[expose, irreducible] def tmZj (j : ℕ) : Array ℕ :=
  conjTab 4060 (tmCGen j) (ruInv (tmCGen j)) tmTZ

@[expose] def tmBasicCheck : Bool :=
  isInvA 4060 ruA0A (ruInv ruA0A) && isInvA 4060 ruA1A (ruInv ruA1A) &&
  lettersOK 2 tmWordA && lettersOK 2 tmWordB && lettersOK 2 tmWordL && lettersOK 2 tmWordZ &&
  lettersOK 4 tmWordG0 && lettersOK 4 tmWordG1 &&
  (List.range 4).all (fun i => lettersOK 2 (tmWordsS.getD i [])) &&
  (List.range 7).all (fun j => lettersOK 2 (tmWordsC.getD j [])) &&
  eqA 4060 (compA 4060 ruA0A ruA0A) (idA 4060) && !eqA 4060 ruA0A (idA 4060) &&
  allLt 4060 fun i => ruA0A[i]! != i

@[expose] def tmABCheck : Bool :=
  isInvA 4060 tmTA (ruInv tmTA) && isInvA 4060 tmTB (ruInv tmTB) &&
  eqA 4060 (compA 4060 tmTA ruA0A) (compA 4060 ruA0A tmTA) &&
  eqA 4060 (compA 4060 tmTB ruA0A) (compA 4060 ruA0A tmTB) &&
  eqA 4060 (powA 4060 tmTA 5) (idA 4060) && !eqA 4060 tmTA (idA 4060) &&
  eqA 4060 (powA 4060 tmTB 7) (idA 4060) && !eqA 4060 tmTB (idA 4060) &&
  eqA 4060 (powA 4060 (compA 4060 tmTA tmTB) 13) (idA 4060) &&
  !eqA 4060 (compA 4060 tmTA tmTB) (idA 4060)

@[expose] def tmZLCheck : Bool :=
  eqA 4060 (compA 4060 tmTZ tmTZ) (idA 4060) && !eqA 4060 tmTZ (idA 4060) &&
  decide (tmZFix < 4060) && tmTZ[tmZFix]! == tmZFix &&
  isInvA 4060 tmTL (ruInv tmTL) && isInvA 4060 tmTAl (ruInv tmTAl) &&
  isInvA 4060 tmTBl (ruInv tmTBl) &&
  eqA 4060 (compA 4060 (compA 4060 tmTL ruA0A) (ruInv tmTL)) (compA 4060 ruA0A tmTZ)

@[expose] def tmGenCheck : Bool :=
  eqA 4060 (wordA 4060 tmGen4 tmGen4i tmWordG0) ruA0A &&
  eqA 4060 (wordA 4060 tmGen4 tmGen4i tmWordG1) ruA1A

@[expose] def tmCentralCover (E : Enum) : Bool :=
  E.tabs.all fun t =>
    t == idTab 4060 || !(comp 4060 t t == idTab 4060) ||
      !(tmSTabs.all fun g => comp 4060 t g == comp 4060 g t) ||
      (List.range 7).any fun j => t == tmZj j

@[expose] def tmSylowCheck : Bool :=
  (List.range 4).all (fun i => isInvA 4060 (tmSGen i) (ruInv (tmSGen i))) &&
  (List.range 7).all (fun j => isInvA 4060 (tmCGen j) (ruInv (tmCGen j))) &&
  tmSTabs.all (fun g => comp 4060 g tmTZ == comp 4060 tmTZ g) &&
  enumOK 4060 tmSTabs tmSEnum && tmSEnum.tabs.size == 64 && tmCentralCover tmSEnum

@[expose] def tmRuCheck : Bool :=
  tmBasicCheck && tmABCheck && tmZLCheck && tmGenCheck && tmSylowCheck

end CFSG.EvenSporadicStandard.Induction.TMemRu
