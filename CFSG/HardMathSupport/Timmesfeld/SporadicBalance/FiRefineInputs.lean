module

public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative

open CFSG.Sporadic.FischerOddCore.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def initX (n : Nat) (t c0 : Array Nat) (pre : List Nat) : Array Nat :=
  let it := initT n t pre
  let m := 2 * pre.length + 4
  Array.ofFn (n := n) fun v => c0[v.val]! * m + it[v.val]!

@[expose] def colourX (n : Nat) (nbr : Array (List Nat)) (t c0 : Array Nat) (pre : List Nat)
    (k : Nat) : Array Nat :=
  refineT n nbr t (initX n t c0 pre) k

@[expose] def boundsXOK (n : Nat) (nbr : Array (List Nat)) (t c0 : Array Nat)
    (pre0 pts bounds : List Nat) (k : Nat) : Bool :=
  pts.length == bounds.length &&
    allLt pts.length (fun s =>
      let c := colourX n nbr t c0 (pre0 ++ pts.take s) k
      cellCount n c c[pts.getD s 0]! == bounds.getD s 0) &&
    colInj n (colourX n nbr t c0 (pre0 ++ pts) k)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative
