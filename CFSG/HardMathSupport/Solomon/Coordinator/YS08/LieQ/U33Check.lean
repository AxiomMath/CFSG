module

public import CFSG.LieType.ChevTwo.OppCl.SmallU33Check

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin

open CFSG.GH74.KGroups CFSG.GH74.KGroups.U33 CFSG.LieType.ChevTwo.OppCl.U33Fin

@[expose] def ta : Equiv.Perm (Fin 28) :=
  List.formPerm [0, 3, 2, 1] * List.formPerm [4, 27, 25, 12] * List.formPerm [5, 8] *
    List.formPerm [6, 19, 18, 16] * List.formPerm [7, 15, 13, 21] * List.formPerm [9, 10, 24, 22] *
    List.formPerm [11, 20] * List.formPerm [14, 17, 26, 23]

@[expose] def tb : Equiv.Perm (Fin 28) :=
  List.formPerm [1, 3] * List.formPerm [4, 24, 10, 15, 7, 18, 19, 27] *
    List.formPerm [5, 23, 11, 14, 8, 17, 20, 26] * List.formPerm [6, 22, 12, 13, 9, 16, 21, 25]

@[expose] def z0 : Equiv.Perm (Fin 28) :=
  List.formPerm [4, 10, 7, 19] * List.formPerm [5, 11, 8, 20] * List.formPerm [6, 12, 9, 21] *
    List.formPerm [13, 16, 25, 22] * List.formPerm [14, 17, 26, 23] * List.formPerm [15, 18, 27, 24]

@[expose] def closureStep (gs L : List (Equiv.Perm (Fin 28))) : List (Equiv.Perm (Fin 28)) :=
  (L ++ L.flatMap fun x => gs.map fun g => x * g).dedup

@[expose] def T0L (_ : Unit := ()) : List (Equiv.Perm (Fin 28)) :=
  (List.range 40).foldl (fun L _ => closureStep [ta, tb] L) [1]

@[expose] def zL : List (Equiv.Perm (Fin 28)) := [1, z0, z0 ^ 2, z0 ^ 3]

@[expose] def t0 : Equiv.Perm (Fin 28) := z0 ^ 2

@[expose] def checkT0 (_ : Unit := ()) : Bool :=
  let T := T0L ()
  let P := elems ()
  T.length == 32 && decide T.Nodup && T.contains 1 &&
    T.all (fun x => T.contains x⁻¹ && P.contains x && T.all fun y => T.contains (x * y))

@[expose] def checkZ (_ : Unit := ()) : Bool :=
  let T := T0L ()
  T.contains z0 && z0 ^ 4 == 1 && z0 ^ 2 != 1 && T.all (fun x => x * z0 == z0 * x) &&
    T.all (fun x => !(T.all fun y => x * y == y * x) || zL.contains x)

@[expose] def checkC (_ : Unit := ()) : Bool :=
  ((elems ()).filter fun x => x * t0 == t0 * x).length == 96

@[expose] def checkE1 (_ : Unit := ()) : Bool :=
  let T := T0L ()
  (elems ()).all fun g =>
    !(g ^ 3 == 1 && g != 1 && g * t0 == t0 * g) ||
      T.all fun x => !(x * g == g * x) || zL.contains x

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.U33Fin
