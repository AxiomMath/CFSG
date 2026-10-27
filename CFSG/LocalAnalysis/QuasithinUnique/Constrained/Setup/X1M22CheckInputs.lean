module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Data
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m22rl : List ↥NativeSporadic.M22 :=
  sylowList NativeSporadic.M22 m22a m22b m22RGens m22RWords

@[expose] def m22conj (ws : List (List ℤ)) : List ↥NativeSporadic.M22 :=
  ws.map (evalN NativeSporadic.M22 [m22a, m22b])

end CFSG.QuasithinUnique.Setup.X1
