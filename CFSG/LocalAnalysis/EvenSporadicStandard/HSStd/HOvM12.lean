module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12

public section

namespace CFSG.EvenSporadicStandard.HSStd.HOv

theorem isElemAb2_of_isElemAbelian {G : Type*} [Group G] {A : Subgroup G}
    (hA : CFSG.Open.IsElemAbelian 2 A) : CFSG.GH74.GLS.Stage1.Thm6.Sec13.IsElemAb2 A :=
  fun a ha => ⟨by simpa [pow_two] using hA.2 a ha,
    fun b hb => congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)⟩

theorem not_exists_elemAbelian_sixteen_of_m12
    {D : Type} [Group D]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic D .M12) :
    ¬ ∃ A : Subgroup D, CFSG.Open.IsElemAbelian 2 A ∧ Nat.card ↥A = 16 := by
  rintro ⟨A, hA, hcard⟩
  have := CFSG.GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three h A (isElemAb2_of_isElemAbelian hA)
  omega

end CFSG.EvenSporadicStandard.HSStd.HOv
