module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHSInputs

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def hsTa' : Array Nat :=
  ((List.range hsData.n).map (ap (hsData.orbit ()).alpha)).toArray

@[expose] def hsTb' : Array Nat :=
  ((List.range hsData.n).map (ap (hsData.orbit ()).beta)).toArray

@[expose] def hsProg2 : List (Nat × Nat) := hsProg ++ hsExt

@[expose] def hsNT2 : Array (Array Nat) := slpTabsA hsTa' hsTb' hsProg2

@[expose] def hsGens2 : List (Array Nat) := hsQp.map fun p => hsNT2[p.1]!

@[expose] def hsGensI2 : List (Array Nat) := hsQp.map fun p => hsNT2[p.2]!

@[expose] def hsEnum2 : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB hsData.n (List.range hsData.n) hsGens2 hsGensI2 100000

@[expose] def hsRl : List (Array Nat) := fullTables hsData.n hsEnum2.1

@[expose] def hsZ1 : List (Array Nat) := zSeries hsRl hsGens2 (Array.range hsData.n) 1

@[expose] def hsQc : List (Array Nat) :=
  cenList hsRl (zSeries hsRl hsGens2 (Array.range hsData.n) 3)

@[expose] def hsWNT : Array (Array Nat) := slpTabsA hsNT2[hsGn]! hsNT2[hsHn]! hsWprog

end CFSG.QuasithinUnique.Setup.X1
