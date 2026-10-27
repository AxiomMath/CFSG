module

public import CFSG.CharacterTheory.Semidihedral.GL2IndexThree

public section

namespace CFSG.Semidihedral.Principal

theorem GL2_three_central_involution_index_three_obstruction {Y : Type*} [Group Y] [Finite Y]
    (t : Y) (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set Y) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    (Subgroup.centralizer ({t} : Set Y)).index ≠ 3 :=
  GL2IndexThree.involution_centralizer_index_ne_three t ht hC.some

end CFSG.Semidihedral.Principal
