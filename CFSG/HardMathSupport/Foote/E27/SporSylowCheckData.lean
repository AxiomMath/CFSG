module

public import CFSG.Sporadic.SmallOddCore.LocalCheck
public meta import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore.Native

@[expose] def sylowCentOK (n cap m : Nat) (gs : List Table) : Bool :=
  let E := (mulClosureH n gs.toArray cap).1.toList
  gs.all (fun g => permOK n g) && enumOK n cap m gs &&
    E.all fun s => !(selOK n [3] s) || (E.countP fun y => commTT n y s) % 81 == 0

structure Wit235 where
  x : Table
  a : Table
  b : Table

@[expose] def wit235OK (n : Nat) (w : Wit235) : Bool :=
  permOK n w.x && permOK n w.a && permOK n w.b && commTT n w.a w.x && commTT n w.b w.x &&
    tblEq n (powT n 2 w.a) (idT n) && tblEq n (powT n 3 w.b) (idT n) &&
    tblEq n (powT n 5 (compT n w.a w.b)) (idT n) && !tblEq n w.a (idT n) &&
    !tblEq n w.b (idT n)

@[expose] def sylowCentWitOK (n cap m : Nat) (gs : List Table) (ws : List Wit235) : Bool :=
  let E := (mulClosureH n gs.toArray cap).1.toList
  gs.all (fun g => permOK n g) && enumOK n cap m gs && ws.all (wit235OK n) &&
    E.all fun s => !(selOK n [3] s) || (E.countP fun y => commTT n y s) % 81 == 0 ||
      ws.any fun w => E.any fun p => tblEq n (compT n p w.x) (compT n s p)

end CFSG.HardMathSupport.Foote.E27
