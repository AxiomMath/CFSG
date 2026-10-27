module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTwinGood
public import CFSG.GH74.KGroups.TwoA7Cover

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.TwinFr

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {L R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem TwinHyp.not_mem_center (h : TwinHyp L R S t) :
    (⟨t, h.mem⟩ : ↥L) ∉ Subgroup.center ↥L := fun hc => by
  obtain ⟨l, hl, hlt⟩ := h.not_central
  exact hlt (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨l, hl⟩))

omit [Finite Y] in
theorem TwinHyp.false_of_sl2 (h : TwinHyp L R S t) (hK : GH74.GLS.HasSL2Model ↥L Odd) :
    False := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := hK
  let e' : ↥L ≃* SL(2, F) := e.trans (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  have ht : (⟨t, h.mem⟩ : ↥L) = e'.symm (-1) :=
    (orderOf_eq_two_iff_of_equiv_sl2 hodd e' _).mp (by rw [Subgroup.orderOf_mk, h.datum.order])
  apply h.not_mem_center
  rw [mem_center_iff_of_equiv_sl2 e', ht, MulEquiv.apply_symm_apply, mem_center_sl2_iff]
  exact Or.inr rfl

theorem TwinHyp.false_of_twoA7 (h : TwinHyp L R S t)
    (hK : GH74.GLS.IsDoubleCoverOfAlt ↥L 7) : False := by
  obtain ⟨π, z, hπ, hcen⟩ := GH74.KGroups.TwoA7.exists_cover hK
  have htt : (⟨t, h.mem⟩ : ↥L) * ⟨t, h.mem⟩ = 1 := Subtype.ext (t_mul_self h.datum)
  rcases hπ.eq_one_or_eq_z_of_sq_eq_one htt with h1 | h1
  · have := h.datum.order
    rw [show t = 1 from congrArg Subtype.val h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · exact h.not_mem_center ((hcen _).mpr (Or.inr h1))

end CFSG.ClassicalInvolution.Q3.TA3.TwinFr
