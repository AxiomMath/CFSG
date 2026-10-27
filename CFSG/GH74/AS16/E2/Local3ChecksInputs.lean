module

public import CFSG.GH74.KGroups.Generic
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups

variable {n : ℕ}

@[expose] def c3list (L : List (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) :
    List (Equiv.Perm (Fin n)) :=
  L.filter fun c => decide (c ^ 3 = 1) && decide (c * t = t * c)

@[expose] def local3Check (L : List (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) : Bool :=
  let cs := c3list L t
  decide (t ∈ L) && decide (t ≠ 1) && decide (t ^ 2 = 1) && cs.any (fun c => decide (c ≠ 1)) &&
    L.all fun a => bif cs.all (fun c => decide (a * c = c * a)) then
      (decide (a = 1) || decide (a = t)) else true

@[expose] def expCheck (L : List (Equiv.Perm (Fin n))) (k m : ℕ) : Bool :=
  L.all fun x => bif decide (x ^ k = 1) then decide (x ^ m = 1) else true

end CFSG.GH74.AS16.E2
