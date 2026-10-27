module

public import CFSG.LargeExtraspecial.CorBWeakClosure
public import CFSG.LargeExtraspecial.S45QLin
public import CFSG.GroupTheory.GL32SylowNonabelian

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Subgroup

theorem false_of_forall_conj_mem_QG_of_mulEquiv_GL32 (hCorB : TimmesfeldCorBInput)
    (hFacts : CorBListFacts) {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G)
    (h : ∀ g : G, g * S.z * g⁻¹ ∈ S.M → g * S.z * g⁻¹ ∈ S.QG)
    (e : S.Mbar ≃* GL (Fin 3) (ZMod 2)) : False := by
  have hQG : S.QG.subgroupOf S.M = S.Q := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr S.QG_le_M]
    rfl
  have hN : (S.QG.subgroupOf S.M).Normal := by
    rw [hQG]
    exact S.normal
  haveI : (S.QG.subgroupOf S.M).Normal := hN
  let ee : (↥S.M ⧸ S.QG.subgroupOf S.M) ≃* GL (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq hQG).trans (S.quotientEquivMbar.trans e)
  have hsimple : IsSimpleGroup (↥S.M ⧸ S.QG.subgroupOf S.M) :=
    (MulEquiv.isSimpleGroup_congr ee).mpr
      (CFSG.LargeExtraspecial.S45Q.isSimpleGroup_GL_zmod_two (by norm_num : 3 ≤ 3))
  have hnonab : ∀ P : Sylow 2 (↥S.M ⧸ S.QG.subgroupOf S.M),
      ∃ x ∈ (P : Subgroup (↥S.M ⧸ S.QG.subgroupOf S.M)),
        ∃ y ∈ (P : Subgroup (↥S.M ⧸ S.QG.subgroupOf S.M)), x * y ≠ y * x :=
    fun P => CFSG.GroupTheory.exists_not_commute_of_sylow_two_of_mulEquiv_GL32 ee P
  exact false_of_forall_conj_mem_QG_of_section hCorB hFacts S h S.M S.QG
    S.QG_le_M le_rfl hN hsimple hnonab

end CFSG.LargeExtraspecial.S8
