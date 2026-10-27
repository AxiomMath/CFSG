module

public import CFSG.CGT.T75O.Class
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction
public import CFSG.CGT.Timmesfeld75.Sec68FromCorB

public section

namespace CFSG.CGT.T75O

open CFSG.CGT.Timmesfeld75 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LinearGroups.UnitaryThreeOverNine

theorem isConj_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {x y : X}
    (h : IsConj (e x) (e y)) : IsConj x y := by
  simpa using MonoidHom.map_isConj e.symm.toMonoidHom h

theorem isConj_of_orderOf_eq_two_psu33 {Y : Type} [Group Y] (h : LieModel Y .PSU 3 3 1)
    {x y : Y} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_of_ne_zero (by norm_num) h
  have hF : Nat.card K = 9 := by
    rw [hK]
    norm_num
  let e' : Y ≃* StatedSU 3 3 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hF)).trans QuotientGroup.quotientBot)
  have hx' : orderOf (e' x) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  have hy' : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hy
  exact isConj_of_mulEquiv e' (isConj_of_orderOf_eq_two hF hx' hy')

theorem sec56_u33_excl : Sec56ExclAt fun Y _ => LieModel Y .PSU 3 3 1 := by
  intro G _ T T₁ c Y _ ⟨e⟩ hU
  refine c.false_of_isConj_involutions fun x y hx hx1 hy hy1 => ?_
  have hx2 : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx) hx1
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by simpa [pow_two] using hy) hy1
  have hcj := isConj_of_orderOf_eq_two_psu33 hU (x := e x) (y := e y)
    (by rw [MulEquiv.orderOf_eq]; exact hx2) (by rw [MulEquiv.orderOf_eq]; exact hy2)
  exact isConj_of_mulEquiv e hcj

end CFSG.CGT.T75O
