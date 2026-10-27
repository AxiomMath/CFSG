module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23Data
public import CFSG.Sporadic.Schreier.M23Gens

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def m23rl : List ↥NativeSporadic.M23 :=
  sylowList NativeSporadic.M23 m23GenA m23GenB m23RGens m23RWords

@[expose] def m23rinv : List ↥NativeSporadic.M23 := invList NativeSporadic.M23 m23rl

@[expose] def m23conj (ws : List (List ℤ)) : List ↥NativeSporadic.M23 :=
  ws.map (evalN NativeSporadic.M23 [m23GenA, m23GenB])

@[expose] def m23G1ok : Bool :=
  m23G1.all fun e => e.2.1.length == 2 && witOK [m23rl.getD e.1 1] (m23conj e.2.1) e.2.2 11

@[expose] def m23G1cover : Bool :=
  m23rinv.all fun x => m23G1.any fun e => m23rl.any fun r => r * x * r⁻¹ == m23rl.getD e.1 1

@[expose] def m23G2ok : Bool :=
  m23G2.all fun e => e.2.2.1.length == 1 &&
    witOK [m23rl.getD e.1 1, m23rl.getD e.2.1 1] (m23conj e.2.2.1) e.2.2.2 11

@[expose] def m23G2cover : Bool :=
  (pairList NativeSporadic.M23 m23rinv).all fun p => m23G2.any fun e =>
    m23rl.any fun r => r * p.1 * r⁻¹ == m23rl.getD e.1 1 && r * p.2 * r⁻¹ == m23rl.getD e.2.1 1

end CFSG.QuasithinUnique.Setup.X1
