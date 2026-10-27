
module

public import CFSG.Fischer.T46UnitaryBase
import all CFSG.Fischer.T46UnitaryBase

public import CFSG.Fischer.T46
import all CFSG.Fischer.F4

public section

namespace CFSG.Fischer

open CFSG.F4.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem range_piSU : piSU.range = T46 :=
  (Subgroup.eq_of_le_of_card_ge T46_le_range (by rw [card_T46]; exact card_range_le)).symm

theorem ker_piSU : piSU.ker = Subgroup.center SU0 := by
  refine (Subgroup.eq_of_le_of_card_ge center_le_ker ?_).symm
  have h1 := card_SU0_eq
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SU0)
  rw [range_piSU, card_T46] at h1
  have h3 := card_psu_le
  have hz : 0 < Nat.card (Subgroup.center SU0) := Nat.card_pos
  nlinarith

noncomputable def suQuotEquiv : (SU0 ⧸ Subgroup.center SU0) ≃* T46 :=
  (QuotientGroup.quotientMulEquivOfEq ker_piSU.symm).trans
    ((QuotientGroup.quotientKerEquivRange piSU).trans (MulEquiv.subgroupCongr range_piSU))

theorem suQuotEquiv_mk (g : SU0) : (suQuotEquiv (QuotientGroup.mk g) : Equiv.Perm (Fin 693)) =
    piSU g := by
  simp only [suQuotEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    MulEquiv.subgroupCongr_apply, QuotientGroup.quotientKerEquivRange,
    MulEquiv.ofBijective_apply, QuotientGroup.rangeKerLift]
  rfl

end CFSG.Fischer
