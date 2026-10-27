module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def harCW3 : List ℕ := [6, 3, 4, 3]

@[expose] def harCW5 : List ℕ := [3, 2, 4, 5, 6, 3, 2, 3, 4, 5, 6, 2, 3, 2]

@[expose] def harCWit : List ℕ := [3, 2, 4, 3, 4, 1, 2, 3]

@[expose] def harCQPairs : List (List ℕ × Bool) :=
  [([3, 1, 2, 3, 3, 1, 2, 3], true), ([1], true), ([1], false),
    ([1, 2, 1, 2, 3, 2, 1, 2, 3], true), ([1, 2, 1, 2, 3, 2, 1, 2, 3], false),
    ([2, 2, 2, 1, 2], true)]

@[expose] def harCRoot : List ℕ := [1, 3, 1, 2, 1, 3, 3, 2, 3]

@[expose] def harCG3 (_ : Unit := ()) : Table := wordTbl 11200 harYs harCW3

@[expose] def harCG5 (_ : Unit := ()) : Table := wordTbl 11200 harYs harCW5

@[expose] def harCGW (_ : Unit := ()) : Table := wordTbl 11200 harYs harCWit

@[expose] def harCQ (_ : Unit := ()) : List Table :=
  harCQPairs.map fun p => tComm 11200 (tU p.1) (if p.2 then harCG3 () else harCG5 ())

@[expose] def harCGens (_ : Unit := ()) : List Table := harU ++ [harCG3 (), harCG5 ()]

@[expose] def harCOK1 (_ : Unit := ()) : Bool :=
  let n := 11200
  let g3 := harCG3 ()
  let g5 := harCG5 ()
  let c := harCGW ()
  tblEq n (compT n (compT n g3 g3) g3) (idT n) && !tblEq n g3 (idT n) &&
  tblEq n (compT n (compT n (compT n (compT n g5 g5) g5) g5) g5) (idT n) && !tblEq n g5 (idT n) &&
  commTT n g3 harZ1 && commTT n g5 harZ1 && commTT n c harZ1 &&
  (harCGens ()).all (fun g => permOK n g && invOK n g (invT n g)) &&
  permOK n c && invOK n c (invT n c)

@[expose] def harCOK2 (_ : Unit := ()) : Bool :=
  let n := 11200
  let qs := harCQ ()
  qs.all (permOK n) && enumOK n 400 128 qs && normOK n 400 qs (harCGens ()) &&
  memT n (mulClosureH n qs.toArray 400).1 (tU harCRoot) &&
  tblEq n (compT n (tU harCRoot) (tU harCRoot)) harZ1

@[expose] def harCOK3 (_ : Unit := ()) : Bool :=
  let n := 11200
  let E := (mulClosureH n harU.toArray 2000).1
  let c := harCGW ()
  let ci := invT n c
  enumOK n 2000 1024 harU &&
    E.all fun y => !tblEq n (compT n y y) harZ2 || !memT n E (conjT n c ci y)

@[expose] def harCOK (_ : Unit := ()) : Bool := harCOK1 () && harCOK2 () && harCOK3 ()

end CFSG.EvenSporadicStandard.TwoHS
