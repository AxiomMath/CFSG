module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
public meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests

public section

namespace CFSG.ComponentClassification.AS81.SuzB0

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.PSL3Four.Native
open CFSG.Sporadic.SuzOddCore

@[expose] def outerTab : Array Nat := (invFullGenArrs 1)[3]!

@[expose] def outerAct : List (Nat × Nat) :=
  [(28, 0), (10, 1), (55, 1), (29, 0), (37, 1), (13, 1)]

@[expose] def oact (i : Nat) : Nat × Nat := outerAct.getD i (0, 0)

@[expose] def outerMat : Array Nat :=
  Array.ofFn (n := 64) fun v =>
    (List.range 6).foldl (fun r i => if v.val.testBit i then r ^^^ (oact i).1 else r) 0

@[expose] def q0SuzCheck : Bool :=
  permOK 1782 outerTab && !(inM outerTab) &&
  (allBelow 6 fun i =>
    eqA 1782 (compA 1782 (compA 1782 outerTab (qArr i)) (invCand 1782 outerTab))
      (compA 1782 qProds[(oact i).1]! (tPow (oact i).2))) &&
  (allBelow matEnum.tabs.size fun j => !(matEnum.tabs[j]! == outerMat))

end CFSG.ComponentClassification.AS81.SuzB0
