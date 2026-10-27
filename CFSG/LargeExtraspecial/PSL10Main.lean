module

public import CFSG.LargeExtraspecial.PSL10Lin
public import CFSG.LargeExtraspecial.PSL10UCount
public import CFSG.LargeExtraspecial.S14C10Alt2
public import CFSG.LargeExtraspecial.OutSixUnitary

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

namespace PSLPSU10

theorem stdHermForm_basisFun (i j : Fin 10) :
    stdHermForm unitaryFieldData_two_one 10 (Pi.basisFun (GaloisField 2 2) (Fin 10) i)
      (Pi.basisFun (GaloisField 2 2) (Fin 10) j) = if i = j then 1 else 0 := by
  rw [Pi.basisFun_apply, Pi.basisFun_apply, stdHermForm_single, Pi.single_apply]

@[expose] noncomputable def psuEquiv :
    timmesfeldPSU 10 ≃* sesqSpecialUnitaryGroup (stdHermForm unitaryFieldData_two_one 10) :=
  (timmesfeldPSUEquiv (by norm_num)).trans
    ((unitarySUEquivPSU unitaryFieldData_two_one (by norm_num) (by norm_num)).symm.trans
      (suEquivUnitarySU unitaryFieldData_two_one (Pi.basisFun _ (Fin 10))
        stdHermForm_basisFun).symm)

theorem pslpsu10Input_psu (X : Type*) [Group X] (hX : Nonempty (X ≃* timmesfeldPSU 10)) (t : X)
    (ht : orderOf t = 2) : Conclusion X t :=
  Conclusion.of_mulEquiv (hX.some.trans psuEquiv)
    (conclusion_unitary (stdHermForm_isSymm _ _) (stdHermForm_separatingLeft _ _)
      (Module.finrank_fin_fun _) (by rwa [MulEquiv.orderOf_eq]))

end PSLPSU10

theorem pslpsu10Input : PSLPSU10Input := fun X _ _ hX t ht =>
  hX.elim (fun h => PSLPSU10.pslpsu10Input_psl X h t ht)
    (fun h => PSLPSU10.pslpsu10Input_psu X h t ht)

end CFSG.LargeExtraspecial.S14
