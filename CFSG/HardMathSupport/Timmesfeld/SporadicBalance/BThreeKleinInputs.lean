module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def kleinPts : Array Nat := #[216, 3062, 5872]

@[expose] def kleinWords : Array (List Nat) :=
  #[[8, 8, 4, 4, 22, 8, 10, 14, 8, 19, 12, 15, 12, 20, 18, 18, 20, 16, 16, 22, 20],
    [15, 17, 10, 4, 16, 10, 20, 8, 14, 14, 17, 13, 17, 18, 16, 20],
    [3, 18, 3, 6, 0, 7, 9, 9, 4, 14, 9, 11, 22, 10, 12, 12, 15, 12, 18, 20, 19, 17],
    [12, 7, 7, 3, 22, 16, 20, 4, 18, 8, 13, 10, 9, 18, 17, 12, 12, 22, 16, 18, 17, 19, 20],
    [3, 0, 14, 3, 4, 11, 5, 5, 22, 17, 8, 19, 12, 15, 12, 16, 16, 16, 16, 20]]

@[expose] def kleinOrders : Array Nat := #[11, 13, 11, 11, 11]

@[expose] def kleinFix : Array (List Nat) :=
  #[[0], [0], [216, 3062], [216, 5872], [3062, 5872]]

@[expose] def kleinZ : List Nat :=
  [19, 7, 3, 0, 13, 19, 7, 4, 15, 8, 14, 9, 22, 18, 13, 20, 18, 16, 16]

@[expose] def baseFixed (T : Table) : Bool := allIn 0 6 fun t => ap T t == t

@[expose] def kleinCheckL (O : WOrbit) (L : Array Table) : Bool :=
  let D := dTable O
  let bi := genTables O (-2)
  (allIn 0 3 fun i => allIn 0 3 fun j => i == j ||
      treeAct O.par O.lab O.alpha O.beta D bi kleinPts[i]! kleinPts[j]! == kleinPts[j]!) &&
    kleinWords.size == 5 && kleinWords.all (fun w => w.all fun z => decide (z < L.size)) &&
    (allIn 0 5 fun k =>
      let Y := qLettersT L kleinWords[k]!
      baseFixed (powT 31671 kleinOrders[k]! Y) && !baseFixed Y &&
        kleinFix[k]!.all fun p => ap Y p == p) &&
    kleinZ.all (fun z => decide (z < L.size)) &&
    (allIn 0 3 fun i => ap (qLettersT L kleinZ) kleinPts[i]! == kleinPts[i]!)

@[expose] def kleinOK (O : WOrbit) : Bool := kleinCheckL O (chainLetters O)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
