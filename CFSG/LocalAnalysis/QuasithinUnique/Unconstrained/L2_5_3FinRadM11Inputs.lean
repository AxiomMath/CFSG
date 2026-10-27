module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadListCheck
public import CFSG.Sporadic.Schreier.M11Data

public section

namespace CFSG.QuasithinUnique.Fin253
open CFSG.Sporadic.Schreier CFSG.Blueprint

@[expose] def m11mul (a b : Equiv.Perm (Fin 11)) : Equiv.Perm (Fin 11) := tab (a * b)

@[expose] def m11inv (a : Equiv.Perm (Fin 11)) : Equiv.Perm (Fin 11) := tab a⁻¹

@[expose] def m11Invs : List (Equiv.Perm (Fin 11)) :=
  m11Elements.filter fun t => decide (t ≠ 1 ∧ m11mul t t = 1)

@[expose] def m11Ord4 : List (Equiv.Perm (Fin 11)) :=
  m11Elements.filter fun u => decide (lpow m11mul 1 u 4 = 1 ∧ lpow m11mul 1 u 2 ≠ 1)

end CFSG.QuasithinUnique.Fin253
