module

public import Certificates.Data.CFSGNative.Timmesfeld.Co1Leaf
public import CFSG.Sporadic.Co1Block.PermData
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeData
public import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import Std.Data.HashMap
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Leaf
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1SplitCheckInputs
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public meta import Std.Data.HashMap

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native

@[expose] def sDag (_ : Unit := ()) : List Rows × List Rows × Bool :=
  dag [aR, bR] (Data.dagWords.map decWord)

@[expose] def lRows (_ : Unit := ()) : List Rows :=
  (List.range 6).map aRows ++ (List.range 3).map gRows ++ (sDag ()).1

@[expose] def lInvs (_ : Unit := ()) : List Rows := (lRows ()).map inv

@[expose] def lCheck (_ : Unit := ()) : Bool :=
  (sDag ()).2.2 && (lRows ()).length == 75 &&
    ((lRows ()).zip (lInvs ())).all fun xy => mul xy.1 xy.2 == one

@[expose] def wordL (w : List Nat) : Rows := word (lRows ()) (lInvs ()) (decWord w)

@[expose] def qGens (_ : Unit := ()) : List Rows := Data.qGenWords.map wordL

@[expose] def qEnum (_ : Unit := ()) : Timmesfeld.Co1Leaf.Enum :=
  Timmesfeld.Co1Leaf.enumBFS (qGens ()) 19683

@[expose] def qCheck (_ : Unit := ()) : Bool :=
  Timmesfeld.Co1Leaf.enumOK (qGens ()) (qEnum ()) 19683

@[expose] def aGens (_ : Unit := ()) : List Rows := (List.range 6).map aRows

@[expose] def eElts (_ : Unit := ()) : List Rows := (Timmesfeld.Co1Leaf.eltsOf (aGens ())).toList

@[expose] def repRows (i : Nat) : Rows := wordL (Data.repWords.getD i [])

@[expose] def rootRows (j : Nat) : Rows := wordL (Data.rootWords.getD j [])

@[expose] def fusCheck (_ : Unit := ()) : Bool :=
  let es := eElts ()
  Data.repWords.length == 42 &&
    Timmesfeld.Co1Leaf.fusOK (qEnum ()) (qGens ()) ((List.range 42).map repRows) es.contains

@[expose] def conjCheck (_ : Unit := ()) : Bool :=
  Data.repWords.length == 42 && Data.repRoot.length == 42 && Data.repConj.length == 42 &&
    (List.range 42).all fun i =>
      decide (Data.repRoot.getD i 0 < 3) &&
        mul (wordL (Data.repConj.getD i [])) (repRows i) ==
          mul (rootRows (Data.repRoot.getD i 0)) (wordL (Data.repConj.getD i []))

@[expose] def xList (_ : Unit := ()) : List Nat := CFSG.Sporadic.Co1Block.certVecs.toList

@[expose] def eLeaves (_ : Unit := ()) : List (List Rows) :=
  aGens () :: (Timmesfeld.Co1Leaf.normVecs 3 6).map (Timmesfeld.Co1Leaf.kerElts 3 (aGens ()))

@[expose] def eCheck (_ : Unit := ()) : Bool :=
  Timmesfeld.Co1Leaf.splitOK [] (aGens ()) && Timmesfeld.Co1Leaf.leavesOK (xList ()) (eLeaves ())

@[expose] def splitRows (j : Nat) : List Rows := (Data.splitBC.getD j []).map wordL

@[expose] def bcLeaves (j : Nat) : List (List Rows) :=
  (Timmesfeld.Co1Leaf.normVecs 3 4).map fun f =>
    rootRows j :: Timmesfeld.Co1Leaf.kerElts 3 (splitRows j) f

@[expose] def bcCheck (j : Nat) : Bool :=
  (splitRows j).length == 4 && Timmesfeld.Co1Leaf.splitOK [rootRows j] (splitRows j) &&
    Timmesfeld.Co1Leaf.leavesOK (xList ()) (bcLeaves j)

@[expose] def planeRows (_ : Unit := ()) : List Rows := Data.planeD.map wordL

@[expose] def dChild (f : List Nat) : List Rows :=
  rootRows 2 :: Timmesfeld.Co1Leaf.kerElts 3 (planeRows ()) f

@[expose] def childPlane (i : Nat) : List Rows := (Data.planesD.getD i []).map wordL

@[expose] def dLeaves (_ : Unit := ()) : List (List Rows) :=
  ((Timmesfeld.Co1Leaf.normVecs 3 2).zipIdx).flatMap fun fi =>
    (Timmesfeld.Co1Leaf.normVecs 3 2).map fun f' =>
      dChild fi.1 ++ Timmesfeld.Co1Leaf.kerElts 3 (childPlane fi.2) f'

@[expose] def dCheck (_ : Unit := ()) : Bool :=
  (planeRows ()).length == 2 && Timmesfeld.Co1Leaf.splitOK [rootRows 2] (planeRows ()) &&
    Data.planesD.length == 4 &&
    ((Timmesfeld.Co1Leaf.normVecs 3 2).zipIdx).all (fun fi =>
      (childPlane fi.2).length == 2 &&
        Timmesfeld.Co1Leaf.splitOK (dChild fi.1) (childPlane fi.2)) &&
    Timmesfeld.Co1Leaf.leavesOK (xList ()) (dLeaves ())

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T.Native

end
