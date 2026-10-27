module

public import CFSG.LargeExtraspecial.S14C10Schur
public import CFSG.LargeExtraspecial.S14C13B2Weak

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem weakSetting_of {t : S.O} [hN : NQHyp S g t] (hSt : Stage S g t)
    (hext : IsExtraspecialPGroup 2 (Nbar S g t)) (h7 : Concl14_7 S g t) :
    WeakSetting S.Mbar t (Nbar S g t) := by
  have haQ := hSt.hyp4.conj_mem
  have htN : t ∈ Nbar S g t := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have htc : ∀ y ∈ Nbar S g t, t * y = y * t := fun y hy =>
    (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
  refine
    { t_mem := Rbar_le_Mbar (Nbar_le_Rbar htN)
      tt := mul_self_of_mem_Lbar S haQ hSt.mem
      t1 := hSt.ne_one
      N_le := fun _ hn => Rbar_le_Mbar (Nbar_le_Rbar hn)
      t_mem_N := htN
      N_comm := fun n hn => commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
      N_norm := fun h hX ht n hn =>
        conj_mem_Nbar_of_mem_Ct haQ ⟨hX, mem_centralizer_singleton_iff.mpr ht⟩ hn
      comm := hN.comm
      center := fun x hx hc => ?_
      sq := hN.sq
      self := h7.1
      nonab := ?_ }
  · have hcx : (⟨x, hx⟩ : Nbar S g t) ∈ center (Nbar S g t) := by
      rw [mem_center_iff]
      intro v
      exact Subtype.ext (hc v v.2).symm
    exact eq_one_or_eq_of_mem_zpowers (mul_self_of_mem_Lbar S haQ hSt.mem)
      (mem_zpowers_of_mem_center_Nbar hext htN hSt.ne_one htc hcx)
  · obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN hSt.ne_one htc
    refine ⟨a, ha, b, hb, fun h => hSt.ne_one ?_⟩
    rw [← hab, h]
    group

end CFSG.LargeExtraspecial.S14
