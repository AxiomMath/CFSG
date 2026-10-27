module

public import CFSG.GH74.Uniqueness.SU.SU13TA3Assem
public import CFSG.GH74.Uniqueness.SU.SU13TA3MFin
public import CFSG.GH74.Uniqueness.SU.SU13TA3Trans

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU13.TA CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem loc10_of_isTwoAlt_of_recognition (hR1 : Recog1) (hR2 : Recog2) {G : Type} [Group G]
    [Finite G] {z : G} (hz : orderOf z = 2)
    (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10) : Nonempty (Loc10 G z) := by
  obtain ⟨π, hπ⟩ := TwoCover.exists_of_isTwoAlt hH
  obtain ⟨c⟩ := hπ.nonempty_cfg
  have hz1 : zH z ≠ 1 := fun h => by
    have : z = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at hz
    omega
  have hzk : zH z ∈ π.ker := by
    rw [← hπ.center_eq_ker (by norm_num)]
    exact Subgroup.mem_center_iff.mpr fun g => mul_zH g
  obtain ⟨f⟩ := nonempty_fpart10 hπ c hzk hz1
  exact ⟨Loc10.transfer ⟨c.elts hπ hzk hz1, f, p3part hπ c hzk hz1,
    mpart10_of_recognition hR1 hR2 hπ c hzk hz1, epart10 hπ c hzk hz1⟩⟩

end CFSG.GH74.Uniqueness.SU.SU13
