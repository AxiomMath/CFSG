module

public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Sporadic.Th.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def arrTable (n : Nat) (t : Array Nat) : Table :=
  Array.ofFn (n := n) fun i => UInt32.ofNat t[i.val]!

@[expose] def invoList (n : Nat) (t : Array Nat) : Bool :=
  (List.range n).all fun i => decide (t[i]! < n) && t[t[i]!]! == i

@[expose] def movesList (n : Nat) (t : Array Nat) : Bool :=
  (List.range n).any fun i => t[i]! != i

@[expose] def fixedCount (n : Nat) (t : Array Nat) : Nat :=
  (List.range n).countP fun i => t[i]! == i

@[expose] def chainTables (n : Nat) (S : Array (Array Nat)) (base : Array Nat) :
    List (List Table) :=
  let L := rawLevels n S base
  (List.range L.size).map fun i =>
    (List.range L[i]!.pts.size).map fun k => arrTable n L[i]!.tr[k]!

end CFSG.ComponentClassification.J2Cover
