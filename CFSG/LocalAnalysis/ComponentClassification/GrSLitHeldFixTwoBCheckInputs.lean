module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public import CFSG.Sporadic.SmallOddCore.HeLocalCheck2
public meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheck
public meta import CFSG.Sporadic.SmallOddCore.HeLocalCheck2
public meta import CFSG.Sporadic.SmallOddCore.ClassSimple
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.ComponentClassification.GrSLit.HeldFix

open CFSG.PSL3Four.Native CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native

@[expose] def hfCTab (w : List Nat) : Tab := wordTabS 8330 hfC1Tabs w

@[expose] def hfCTab42 (w : List Nat) : Tab := wordTabS 42 heXTabs w

@[expose] def hfRep (k : Nat) (w : List Nat) : List Nat := (List.replicate k w).flatten

@[expose] def hfCommTabs42 : Array Tab :=
  Array.ofFn (n := 3) fun i =>
    let x := hfCTab42 (hfCommWords.getD (2 * i.val) [])
    let y := hfCTab42 (hfCommWords.getD (2 * i.val + 1) [])
    commTab 42 x y (invTab 42 x) (invTab 42 y)

@[expose] def hfOrd7Tabs42 : Array Tab :=
  Array.ofFn (n := 2) fun i => hfCTab42 (hfOrd7Words.getD i.val [])

@[expose] def hfOrd3Tabs42 : Array Tab :=
  Array.ofFn (n := 3) fun i => hfCTab42 (hfOrd3Words.getD i.val [])

@[expose] def hfCommEnum42 : Enum := enumBFS 42 hfCommTabs42 10752

@[expose] def hfOrd7Enum42 : Enum := enumBFS 42 hfOrd7Tabs42 10752

@[expose] def hfOrd3Enum42 : Enum := enumBFS 42 hfOrd3Tabs42 10752

end CFSG.ComponentClassification.GrSLit.HeldFix
