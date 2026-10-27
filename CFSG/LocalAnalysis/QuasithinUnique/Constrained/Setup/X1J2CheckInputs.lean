module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def j2NT : Array (Array Nat) := slpTabsA j2Data.ta j2Data.tb j2Data.prog

@[expose] def j2RG : List (Array Nat) := j2Data.qp.map fun p => j2NT[p.1]!

@[expose] def j2RGi : List (Array Nat) := j2Data.qp.map fun p => j2NT[p.2]!

@[expose] def j2Enum : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB 315 (List.range 315) j2RG j2RGi 100000

@[expose] def j2Keys : Std.HashMap Nat Nat := keyMap 315 j2Enum.1

@[expose] def j2T : Array (Array Nat) := treeTabs 315 4725 j2Data.ta j2Data.tb j2Data.par j2Data.gen

@[expose] def j2U : Array (Array Nat) := treeInvTabs 315 4725 j2Data.tai j2Data.tbi j2Data.par j2Data.gen

@[expose] def j2ONodes : Array (Array Nat) := slpTabsA j2Data.Aa j2Data.Ab j2Data.prog

@[expose] def j2ROm : List (Array Nat) := j2Data.qp.map fun p => j2ONodes[p.1]!

@[expose] def j2Blocks : Array (Array Bool) :=
  blocksOf j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen j2Data.xs

@[expose] def j2Reps : List Nat := repList 4725 j2Data.repR

@[expose] def j2Orbs : List (Nat × Array Bool) := repOrbs j2ROm 4725 j2Reps

end CFSG.QuasithinUnique.Setup.X1
