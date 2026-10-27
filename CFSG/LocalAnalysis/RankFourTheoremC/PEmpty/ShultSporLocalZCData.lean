module

public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Blueprint

namespace PermGens

@[expose] def m22a : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def m22b : Equiv.Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem M22_eq : NativeSporadic.M22 = Subgroup.closure ({m22a, m22b} : Set (Equiv.Perm (Fin 22))) :=
  rfl

end PermGens

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
