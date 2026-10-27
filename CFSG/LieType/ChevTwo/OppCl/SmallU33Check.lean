module

public import CFSG.GH74.KGroups.U33Inputs

public section

namespace CFSG.LieType.ChevTwo.OppCl.U33Fin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33

@[expose] def elems (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) := elemsT QP

@[expose] def invsOf (L : List (Equiv.Perm (Fin 28))) : List (Equiv.Perm (Fin 28)) :=
  L.filter fun s => s * s == 1 && s != 1

@[expose] def o3Of (L : List (Equiv.Perm (Fin 28))) : List (Equiv.Perm (Fin 28)) :=
  L.filter fun x => x ^ 3 == 1 && x != 1

@[expose] def checkCenter (_ : Unit := ()) : Bool :=
  (elems ()).all fun g => !(g * pa == pa * g && g * pb == pb * g) || g == 1

@[expose] def checkExp (_ : Unit := ()) : Bool :=
  (elems ()).all fun x => !(x ^ 27 == 1) || x ^ 3 == 1

@[expose] def checkF1' (L I : List (Equiv.Perm (Fin 28))) : Bool :=
  L.all fun g => !(g ^ 7 == 1 && g != 1) || I.all fun s => !(g * s == s * g)

@[expose] def checkF3' (I O : List (Equiv.Perm (Fin 28))) : Bool :=
  O.all fun g => O.all fun h =>
    !(g * h == h * g && h != g && h != g * g) ||
      [g, h, g * h, g * h * h].any fun x => I.all fun s => !(x * s == s * x)

@[expose] def checkX5g (Cg I : List (Equiv.Perm (Fin 28))) (g : Equiv.Perm (Fin 28)) : Bool :=
  I.all fun s => !(g * s == s * g) ||
    Cg.any fun c => (s * (c * s * c⁻¹)) ^ 3 == 1 && s * (c * s * c⁻¹) != 1

@[expose] def checkX5' (L I O : List (Equiv.Perm (Fin 28))) : Bool :=
  O.all fun g => if I.any (fun s => g * s == s * g) then
    checkX5g (L.filter (fun c => g * c == c * g)) I g else true

@[expose] def checkF1 (_ : Unit := ()) : Bool := checkF1' (elems ()) (invsOf (elems ()))

@[expose] def checkF3 (_ : Unit := ()) : Bool := checkF3' (invsOf (elems ())) (o3Of (elems ()))

@[expose] def checkX5 (_ : Unit := ()) : Bool :=
  checkX5' (elems ()) (invsOf (elems ())) (o3Of (elems ()))

end CFSG.LieType.ChevTwo.OppCl.U33Fin
