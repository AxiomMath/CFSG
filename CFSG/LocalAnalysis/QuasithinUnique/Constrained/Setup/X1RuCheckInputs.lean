module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Th.Native (ap)
open CFSG.Sporadic.Ru.Native (ruData)

@[expose] def ruTa' : Array Nat :=
  ((List.range ruData.n).map (ap (ruData.orbit ()).alpha)).toArray

@[expose] def ruTb' : Array Nat :=
  ((List.range ruData.n).map (ap (ruData.orbit ()).beta)).toArray

@[expose] def ruB' : List Nat := ruData.base.toList

@[expose] def ruProg2 : List (Nat × Nat) := ruProg ++ ruExt

@[expose] def ruNT2 : Array (Array Nat) := slpTabsA ruTa' ruTb' ruProg2

@[expose] def ruGens2 : List (Array Nat) := ruQp.map fun p => ruNT2[p.1]!

@[expose] def ruGensI2 : List (Array Nat) := ruQp.map fun p => ruNT2[p.2]!

@[expose] def ruEnum2 : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB ruData.n ruB' ruGens2 ruGensI2 100000

@[expose] def ruP : List Nat := ptsOf ruB' ruGens2

@[expose] def ruL1 : List (Array Nat) := ruNodes1.map fun i => ruNT2[i]!

@[expose] def ruL2 : List (Array Nat) := ruNodes2.map fun i => ruNT2[i]!

@[expose] def ruL3 : List (Array Nat) := ruNodes3.map fun i => ruNT2[i]!

@[expose] def ruWNT : Array (Array Nat) := slpTabsA ruNT2[ruGn]! ruNT2[ruHn]! ruWprog

end CFSG.QuasithinUnique.Setup.X1
