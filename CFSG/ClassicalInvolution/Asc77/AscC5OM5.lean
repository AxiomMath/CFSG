module

public import CFSG.ClassicalInvolution.GenericLocal.SL2Automorphisms

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open scoped MatrixGroups

theorem two_mul_card_le_of_perfect {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) (P : Subgroup (MulAut SL(2, F))) (hP : ⁅P, P⁆ = P) :
    2 * Nat.card P ≤ Nat.card SL(2, F) := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  have hle := CFSG.ClassicalInvolution.perfect_subgroup_le_range_conj h4 P
  have hcard := CFSG.ClassicalInvolution.natCard_conj_range_of_equiv_sl2 hodd
    (MulEquiv.refl SL(2, F))
  have hfin : Finite (MulAut SL(2, F)) := inferInstance
  have hPle : Nat.card P ≤ Nat.card (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range :=
    Subgroup.card_le_of_le hle
  omega

end CFSG.ClassicalInvolution.Asc77.C5O.M
