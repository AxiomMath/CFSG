module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12Data
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m12rl : List ↥NativeSporadic.M12 :=
  sylowList NativeSporadic.M12 m12a m12b m12RGens m12RWords

@[expose] def m12conj (ws : List (List ℤ)) : List ↥NativeSporadic.M12 :=
  ws.map (evalN NativeSporadic.M12 [m12a, m12b])

end CFSG.QuasithinUnique.Setup.X1
