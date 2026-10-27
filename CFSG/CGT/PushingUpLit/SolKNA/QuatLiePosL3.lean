module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
import CFSG.CGT.PushingUpLit.SolKNA.QuatSporadic
import CFSG.GH74.KGroups.L33
public import CFSG.GH74.KGroups.L33Inputs

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.GH74.KGroups.L33 (QP13 equiv_of_lieModel equiv_P13_P)

theorem posModel_L3 : PosModel .PSL 3 := by
  intro X _ _ h Q hQ
  obtain ⟨e⟩ := equiv_of_lieModel h
  obtain ⟨e'⟩ := equiv_P13_P
  let ψ : X →* Equiv.Perm (Fin 13) :=
    QP13.originalSubgroup.subtype.comp (e.trans e'.symm).toMonoidHom
  exact nonempty_equiv_quaternionGroup_two_of_perm hQ (Ω := Fin 13) (by simp) ψ
    (Subtype.val_injective.comp (e.trans e'.symm).injective)

end CFSG.CGT.PushingUpLit.SolKNA
