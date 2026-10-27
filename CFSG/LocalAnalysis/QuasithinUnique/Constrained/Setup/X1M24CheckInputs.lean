module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Data
public import CFSG.Sporadic.Mathieu.M24

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m24rg : List ↥NativeSporadic.M24 :=
  sylowGens NativeSporadic.M24 m24a m24b m24RGens

@[expose] def m24rl : List ↥NativeSporadic.M24 :=
  sylowList NativeSporadic.M24 m24a m24b m24RGens m24RWords

@[expose] def m24pool : List ↥NativeSporadic.M24 :=
  m24PoolWords.map (evalN NativeSporadic.M24 [m24a, m24b])

@[expose] def m24conj (ws : List (List ℤ)) : List ↥NativeSporadic.M24 :=
  ws.map fun w => m24pool.getD (w.headD 0).toNat 1

@[expose] def m24key (x : ↥NativeSporadic.M24) : ℕ :=
  (List.finRange 24).foldl (fun acc i => acc * 24 + (x.1 i).val) 0

end CFSG.QuasithinUnique.Setup.X1
