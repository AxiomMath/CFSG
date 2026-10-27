module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22GuestRankData
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
  CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
  CFSG.AGLEmbedding.KFactProofs.Fi22Guest

set_option compiler.extract_closed false

@[expose] def signedWord (w : Word) : List Int :=
  w.map fun l => if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def nw1 : List Int :=
  [-2, -2, -2, -1, -2, -1, -2, -1, -2, -2, -2, -2, -1, -2, -2, -1, -2, -2, -2, -2, -2, -2, -1,
   2, 2, 2, -1, -2, -1, -2, -2, -2, -2, -2, -2, -2, -1, -2, -2, -2, -2, -2, -2, -1, 2, 2, -1,
   -1, -2, -1, -2, -1, -2, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 2, 2, 2, 2, -1, 2,
   -1, -2, -2, -2, -2, -2, -2, -2, -1, -1, -2, -2, -2, -1, -2, -2, -2, -1, 2, -1, 2, 2, -1, 2,
   -1, 2, -1, -2, -2, -1, -1, 2, -1, -2, -2, -2, -2, -2, -1, 2, 2, 2, 2, 1, 2, 2, 1, -2, -2,
   -2, -2, -2, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, -2, 1, -2, -2, -2, 1,
   2, 2, 2, 1, 2, 2, -1, -2, 1, -2, -2, -2, -2, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2,
   -1, 2, -1, -2, -1, -2, -2, -2, -2, 1, -2, -2, -2, -2, 1, -2, 1, 2, 1, 2, 2, 2, 2, 2, -1,
   -2, -1, 2, 2, 2, 2, -1, 2, -1, -2, -1, -2, -2, -2, -2, -2, -2, -2, -2, -1, -2, -1, 2, -1,
   2, -1, 2, 2, 2, 2, 2, 1, -2, 1, -2, -1, -2, -2, -2, -2, 1, -2, 1, 2, 1, 2, 2, 2, 2, 2, 1,
   -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, -2, -1, 2, 2, -1, -2, -1]

@[expose] def nw2 : List Int :=
  [-2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -2, -2, -2, -2,
   -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -1, -2, -2, -1, 2, 2, 2, -1, -2, -1, 2, 2, 2, 2, 2,
   2, -1, -2, -2, -2, -2, -1, -2, -1, -2, -1, -2, -2, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1,
   2, 2, 2, 2, 2, -1, 2, -1, -2, -2, -2, -2, -2, -2, -2, -1, -1, -2, -2, -2, -1, -2, -2, -2,
   -1, 2, -1, 2, 2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -2, -1, 2, 2, 2,
   -1, 2, 2, 2, 2, 2, 2, -1, -2, -2, -2, -2, -2, -1, 2, -1, 2, 2, 2, 2, 1, -2, -2, -2, -2, -2,
   -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2,
   -1, -2, -2, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, 2, 2, 2, 2, 1, -2, 1, -2, -1, -2, -2,
   -2, -2, 1, -2, 1, 2, 1, 2, 2, 2, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, -2, -1, 2,
   2, -1, -2]

@[expose] def hw : List Int :=
  [2, 2, 2, 1, 2, 1, -2, 1, -2, -2, -2, -2, -2, 1, 2, 2, 2, 2, 2, -1, 2, -1, -2, -1, -2, -2,
   -2]

@[expose] def uw : List Int :=
  [1, -2, -1, 2, 2, 2, 2, 2, 2, 1, -2, -2, -2, -2, -2, -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, -2,
   -1, -2, -2, -2, -2, -1, -2, -2, -2, -2, -1, -2, -2, 1, -2, -2, -2, 1, 2, 2, 2, 2, 1, -2,
   -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, -2, -2, -2, -2, -1, -2, -2,
   1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, -2, -2, 1, 2, 2, 1, -2, -2, -2, -2, 1, -2, -1, -2, -2, 1,
   2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, -2, 1, -2, 1, 2, 2, 1, -2, 1, -2, -2, -2, 1, 2, 2, 1,
   2, 2, 1, -2, 1, -2, -2, -2, -2, -1, -2, -2, 1, 2, 2, 1, 2, 2, 2, 2, 1, 2, 1, -2, -2, 1, 2,
   2, 1, -2, -2, -2, -2, 1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, -2, 1, 2,
   1, -2, -2, -2, -2, 1, 2, 2, 1, 2, 2, 2, -1, 2, 2, 2, -1, -2, -2, -2, -2, -2, -2, -2, -2, 1,
   2, -1, 2, -1, -2, -2, -2, -2]

@[expose] def conjWords : List (Nat × Nat × List Nat) :=
  [(0, 1, [2, 2, 2, 1, 2]),
   (0, 2, [1, 2, 1, 2, 1, 2]),
   (0, 3, [2, 1, 2]),
   (0, 4, [2, 1, 1]),
   (1, 0, []),
   (1, 1, [2, 2, 2, 2, 1, 2]),
   (1, 2, [2, 2, 1, 2, 1, 2]),
   (1, 3, [1, 1, 2, 1, 1]),
   (1, 4, [2, 2, 2, 2, 2]),
   (2, 0, [2, 2]),
   (2, 1, [1, 1, 2, 1, 2]),
   (2, 2, [1, 1]),
   (2, 3, [1]),
   (2, 4, [2, 1, 1, 2, 1, 1]),
   (3, 0, [2, 2, 2, 2, 2, 2]),
   (3, 1, [1, 2, 1, 2]),
   (3, 2, [2, 2, 2]),
   (3, 3, [2, 2, 1, 2]),
   (3, 4, [2, 1, 2, 1, 2]),
   (4, 0, [2, 2, 2, 2]),
   (4, 1, [2]),
   (4, 2, [2, 1, 2, 1, 1]),
   (4, 3, [1, 2, 1, 1]),
   (4, 4, [1, 2])]

@[expose] def gensInv : Array (Array Nat) := fi22OrigArrs.map (invCand 3510)

@[expose] def evalW (w : List Int) : Array Nat := wordA 3510 fi22OrigArrs gensInv w

@[expose] def xA : Array Nat := evalW (signedWord wx)

@[expose] def yA : Array Nat := evalW (signedWord wy)

@[expose] def n1A : Array Nat := evalW nw1

@[expose] def n2A : Array Nat := evalW nw2

@[expose] def hA : Array Nat := evalW hw

@[expose] def wA : Array Nat := evalW uw

@[expose] def uA : Array Nat := compA 3510 fi22GraphOuterArr wA

@[expose] def pw (A : Array Nat) (k : Nat) : Array Nat :=
  CFSG.Sporadic.FischerOddCore.Native.powA 3510 A k

@[expose] def planeA (i j : Nat) : Array Nat := compA 3510 (pw xA i) (pw yA j)

@[expose] def commA (A B : Array Nat) : Bool := eqA 3510 (compA 3510 A B) (compA 3510 B A)

@[expose] def nProd (w : List Nat) : Array Nat :=
  w.foldr (fun k A => compA 3510 (if k = 1 then n1A else n2A) A) (idA 3510)

@[expose] def conjOK (t : Nat × Nat × List Nat) : Bool :=
  eqA 3510 (compA 3510 (nProd t.2.2) xA) (compA 3510 (planeA t.1 t.2.1) (nProd t.2.2))

@[noinline, expose] def orbCheck : Bool :=
  lettersOK 2 (signedWord wx) && lettersOK 2 (signedWord wy) && lettersOK 2 nw1 &&
  lettersOK 2 nw2 && eqA 3510 (pw xA 5) (idA 3510) && eqA 3510 (pw yA 5) (idA 3510) &&
  commA xA yA &&
  allLt 5 (fun i => allLt 5 fun j => (i == 0 && j == 0) || !(eqA 3510 (planeA i j) (idA 3510))) &&
  eqA 3510 (compA 3510 n1A xA) (compA 3510 (planeA 2 3) n1A) &&
  eqA 3510 (compA 3510 n1A yA) (compA 3510 (planeA 1 2) n1A) &&
  eqA 3510 (compA 3510 n2A xA) (compA 3510 (planeA 4 1) n2A) &&
  eqA 3510 (compA 3510 n2A yA) (compA 3510 (planeA 1 1) n2A) &&
  allLt 5 (fun i => allLt 5 fun j => (i == 0 && j == 0) ||
    conjWords.any fun t => t.1 == i && t.2.1 == j && conjOK t)

@[expose] def fivePts : List Nat := [48, 752, 788, 1425, 847, 221]

@[expose] def fiveBounds : List Nat := [10, 3, 2, 2, 5, 2]

@[noinline, expose] def boundCheck : Bool :=
  boundsOK 3510 fi22Nbr xA fivePts fiveBounds 4 && fiveBounds.prod == 1200

@[expose] def yConj (v : Array Nat) (a : Nat) : Array Nat :=
  compA 3510 (pw yA a) (compA 3510 v (pw yA (5 - a)))

@[expose] def starElt (v : Array Nat) (a b : Nat) : Array Nat :=
  compA 3510 (pw (yConj v a) 7) (yConj v b)

@[expose] def starOK (v : Array Nat) : Bool :=
  eqA 3510 v (idA 3510) || !(eqA 3510 (pw v 8) (idA 3510)) ||
    (List.range 5).any fun a => (List.range 5).any fun b =>
      !(eqA 3510 (pw (starElt v a b) 8) (idA 3510))

@[expose] def gens3 : Array (Array Nat) := #[xA, yA, hA]

@[expose] def centClosure : Array (Array Nat) × Array Nat × Array Nat × Array Nat :=
  closureSearch 3510 gens3 700

@[expose] def centGensOK : Bool :=
  lettersOK 2 hw && lettersOK 2 uw && commA hA xA && commA uA xA && !(fi22InP uA)

@[expose] def centClosureOK : Bool :=
  closureOK 3510 gens3 centClosure.1 centClosure.2.1 centClosure.2.2.1 centClosure.2.2.2 &&
    centClosure.1.size == 600 && keysOK 3510 fivePts centClosure.1

@[expose] def centStarOK : Bool := allLt centClosure.1.size fun i => starOK centClosure.1[i]!

@[noinline, expose] def centCheck : Bool := centGensOK && centClosureOK && centStarOK

end CFSG.AGLEmbedding.KFactProofs.Fi22Five
