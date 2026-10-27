module

public import CFSG.GH74.KGroups.U33Inputs
public meta import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.LargeExtraspecial.S63

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.Sporadic.Schreier

@[expose] def u33Two (x : Equiv.Perm (Fin 28)) : Bool := decide (x ^ 32 = 1)

@[expose] def u33Cent (L : List (Equiv.Perm (Fin 28))) (s : Equiv.Perm (Fin 28)) :
    List (Equiv.Perm (Fin 28)) :=
  L.filter fun c => decide (c * s = s * c)

@[expose] def u33Core (C : List (Equiv.Perm (Fin 28))) : List (Equiv.Perm (Fin 28)) :=
  let C3 := C.filter fun c => decide (c ^ 3 = 1)
  C.filter fun x => u33Two x && C3.all fun c => u33Two (tab (x * (c * x * c⁻¹)))

@[expose] def u33InvCheck (L : List (Equiv.Perm (Fin 28))) (s : Equiv.Perm (Fin 28)) : Bool :=
  let C := u33Cent L s
  let P := u33Core C
  P.length == 16 &&
  C.all (fun t => !decide (t * t = 1) || P.any fun p => decide (p = t)) &&
  P.any fun q => decide (q * q = s) && C.all (fun c => decide (q * c = c * q)) &&
    P.all fun n => !(P.all fun m => decide (n * m = m * n)) ||
      [1, q, q * q, q * q * q].any fun r => decide (r = n)

@[expose] def u33CentCheck : Bool :=
  let L := elemsT QP
  L.all fun s => !decide (s * s = 1) || decide (s = 1) || u33InvCheck L s

end CFSG.LargeExtraspecial.S63
