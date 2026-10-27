module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataM12

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Z2

open CFSG.CGT.PushingUpLit.CGT6M CFSG.Sporadic.Bridge

@[expose] def m12HeisA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 6, 1] * List.formPerm [2, 11, 5] * List.formPerm [4, 9, 10]

@[expose] def m12HeisB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 1, 9] * List.formPerm [2, 6, 11] * List.formPerm [3, 7, 8] *
    List.formPerm [4, 10, 5]

@[expose] def m12HeisC : Equiv.Perm (Fin 12) := m12HeisA * m12HeisB * m12HeisA⁻¹ * m12HeisB⁻¹

@[expose] def m12HeisWordA : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true),
   (1, true)]

@[expose] def m12HeisWordB : List (ℕ × Bool) := [(0, true), (1, true), (0, true)]

@[expose] def m12HeisWordH : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true),
   (1, true), (0, true), (1, true)]

@[expose] def m12HeisH : Equiv.Perm (Fin 12) := wordProd m12Gen m12HeisWordH

end CFSG.AGLEmbedding.KFactProofs.M12Z2
