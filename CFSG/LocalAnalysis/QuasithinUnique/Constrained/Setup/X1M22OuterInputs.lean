module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.Sporadic.Mathieu.M22

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def m22outerOK (r : Equiv.Perm (Fin 22)) (e : List (List ℤ) × List ℤ) : Bool :=
  let ks := e.1.map (evalG [m22gA, m22gB])
  let z := evalG (ks.map fun x => r * (x * r * x⁻¹)) e.2
  ks.length == 3 && decide (z ^ 11 = 1 ∧ z ≠ 1)

end CFSG.QuasithinUnique.Setup.X1
