module

public import CFSG.GH74.Uniqueness.SU.SU13TA9EPart
public import CFSG.GH74.Uniqueness.SU.SU13TA9Trans9E
public import CFSG.GH74.Uniqueness.SU.SU13TA9Assem

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13.TA.L9

theorem loc9_of_isTwoAlt {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9) : Nonempty (Loc9 G z) := by
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hH
  obtain ⟨c⟩ := hπ.nonempty_cfg9
  have hz1 : zH z ≠ 1 := fun h => by
    have : z = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hz
    omega
  have hzk : zH z ∈ π.ker := by
    rw [← hπ.center_eq_ker (by norm_num)]
    exact Subgroup.mem_center_iff.mpr fun g => mul_zH g
  have hfin := hπ.finite'
  obtain ⟨E, hE3, hEmap⟩ := hπ.exists_lift_isPGroup_three
    (IsPGroup.of_card (n := 3) (by rw [card_Ebar]; norm_num) : IsPGroup 3 Ebar)
  have hE : IsE π E := ⟨hE3, hEmap⟩
  obtain ⟨f, hf⟩ := exists_fpart9 hπ c hzk hz1
  obtain ⟨ep, rfl⟩ := exists_epart9 hπ c hE hzk hz1 f.toFPart hf
  exact ⟨Loc9.transfer ⟨c.elts hπ hzk hz1, c.elts9 hπ hzk hz1, f, p3part hπ c hzk hz1, ep,
    mpart9 hπ c hE hzk hz1⟩⟩

end CFSG.GH74.Uniqueness.SU.SU13
