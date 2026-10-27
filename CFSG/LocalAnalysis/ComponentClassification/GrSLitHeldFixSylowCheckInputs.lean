
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public import CFSG.Sporadic.HeldB.InnerCheckBase
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Sporadic.SmallOddCore.ClassSimple
public import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowData
public meta import CFSG.Sporadic.HeldB.InnerCheckBase
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import CFSG.Sporadic.SuzOddCore.RestrictDefs
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def hfC1Tabs : Array Tab := Array.ofFn (n := 9) fun j => heInnerC1 j.val

@[expose] def hfAUArrs : Array (Array Nat) := #[heGen 0, heGen 1, heUArr]

@[expose] def hfXTab : Tab := wordA 8330 hfAUArrs (hfAUArrs.map (invCand 8330)) hfXWord

@[expose] def hfTTabs : Array Tab :=
  Array.ofFn (n := 5) fun j =>
    if j.val = 0 then heT1Arr else wordTabS 8330 hfC1Tabs (hfTauWords.getD (j.val - 1) [])

@[expose] def hfYLetterTabs : Array Tab :=
  Array.ofFn (n := 10) fun j => if j.val < 9 then heInnerC1 j.val else hfXTab

@[expose] def hfYTab : Tab := wordTabS 8330 hfYLetterTabs hfYWord

@[expose] def hfT0Tabs : Array Tab :=
  Array.ofFn (n := 6) fun j => if j.val < 5 then hfTTabs[j.val]! else hfYTab

@[expose] def hfT0Enum : Enum := enumBFS 8330 hfT0Tabs 2048

@[expose] def hfEATab : Tab := wordTabS 8330 hfTTabs (hfEWords.getD 1 [])

@[expose] def hfRes (t : Tab) : Tab := restrictArr hfDelta32 t

@[expose] def hfTTabs32 : Array Tab := hfTTabs.map hfRes

@[expose] def hfT0Tabs32 : Array Tab := hfT0Tabs.map hfRes

@[expose] def hfETabs32 : Array Tab :=
  Array.ofFn (n := 6) fun i => wordTabS 32 hfTTabs32 (hfEWords.getD i.val [])

@[expose] def hfTEnum32 : Enum := enumBFS 32 hfTTabs32 1024

@[expose] def hfT0Enum32 : Enum := enumBFS 32 hfT0Tabs32 2048

@[expose] def hfEEnum32 : Enum := enumBFS 32 hfETabs32 64

@[expose] def hfCands (m : Nat) (TT : Array Tab) (a b : Tab) : List Nat :=
  (List.range TT.size).filter fun k =>
    comp m TT[k]! TT[k]! == idTab m && comp m TT[k]! a == comp m a TT[k]! &&
      comp m TT[k]! b == comp m b TT[k]!

@[expose] def hfE8OK (m : Nat) (x y z : Tab) : Bool :=
  comp m x x == idTab m && comp m y y == idTab m && comp m z z == idTab m &&
    comp m x y == comp m y x && comp m x z == comp m z x && comp m y z == comp m z y &&
    !(x == idTab m) && !(y == idTab m) && !(y == x) && !(z == idTab m) && !(z == x) &&
    !(z == y) && !(z == comp m x y)

@[expose] def hfFindE8 (m : Nat) (TT : Array Tab) (C : List Nat) : Option (Nat × Nat × Nat) :=
  C.findSome? fun i => C.findSome? fun j =>
    if comp m TT[i]! TT[j]! == comp m TT[j]! TT[i]! && !(TT[i]! == TT[j]!) &&
        !(TT[i]! == idTab m) && !(TT[j]! == idTab m) then
      C.findSome? fun k => if hfE8OK m TT[i]! TT[j]! TT[k]! then some (i, j, k) else none
    else none

@[expose] def hfTripleOK (m : Nat) (TT : Array Tab) (a b : Tab) (i j k : Nat) : Bool :=
  decide (i < TT.size) && decide (j < TT.size) && decide (k < TT.size) &&
    hfE8OK m TT[i]! TT[j]! TT[k]! &&
    [TT[i]!, TT[j]!, TT[k]!].all fun t => comp m t a == comp m a t && comp m t b == comp m b t

@[expose] def hfPairOK (m : Nat) (TT : Array Tab) (a b : Tab) : Bool :=
  match hfFindE8 m TT (hfCands m TT a b) with
  | some (i, j, k) => hfTripleOK m TT a b i j k
  | none => false

@[expose, noinline] def hfOuterE8Check (m : Nat) (TT A : Array Tab) : Bool :=
  let idx := indexOf TT
  allBelow A.size fun i =>
    found idx TT A[i]! || !(comp m A[i]! A[i]! == idTab m) ||
      allBelow TT.size fun j =>
        !(comp m TT[j]! TT[j]! == idTab m) || !(comp m TT[j]! A[i]! == comp m A[i]! TT[j]!) ||
          hfPairOK m TT A[i]! TT[j]!

end CFSG.ComponentClassification.GrSLit.HeldFix
