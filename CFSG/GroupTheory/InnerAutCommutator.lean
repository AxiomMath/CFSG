module

public import CFSG.Fischer.Aut.TwoPower

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

theorem le_innerAut_of_commutator_zpowers_conj {X : Type*} [Group X] (b : X)
    {S : Subgroup (MulAut X)}
    (hS : ⁅S, Subgroup.zpowers (MulAut.conj b)⁆ = S) :
    S ≤ (MulAut.conj : X →* MulAut X).range := by
  haveI : ((MulAut.conj : X →* MulAut X).range).Normal := CFSG.Fischer.innerAut_normal
  calc S = ⁅S, Subgroup.zpowers (MulAut.conj b)⁆ := hS.symm
    _ ≤ ⁅S, (MulAut.conj : X →* MulAut X).range⁆ :=
        Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr ⟨b, rfl⟩)
    _ ≤ (MulAut.conj : X →* MulAut X).range := Subgroup.commutator_le_right _ _

end CFSG.GroupTheory

end