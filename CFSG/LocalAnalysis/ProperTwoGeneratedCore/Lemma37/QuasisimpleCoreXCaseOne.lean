module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXConfig
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOne

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X]

namespace BaseConfig

variable {Y : Subgroup X} {e : X}

theorem isStronglyEmbedded_subgroupOf (hc : BaseConfig Y e) {W : Subgroup X} (heW : e ∉ W)
    (hWY : ¬ W ≤ Y) {t : X} (htW : t ∈ W) (htY : t ∈ Y) (ht : orderOf t = 2) :
    BenderSuzuki.IsStronglyEmbedded (Y.subgroupOf W) := by
  refine ⟨fun htop => hWY (Subgroup.subgroupOf_eq_top.mp htop),
    ⟨⟨t, htW⟩, Subgroup.mem_subgroupOf.mpr htY,
      isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ht])⟩, ?_⟩
  intro g hg y hyB hyconj hyinv
  have hgY : (g : X) ∉ Y := fun h => hg (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hyconj
  have hgy : (g : X) * y * (g : X)⁻¹ ∈ Y := by
    have heq : (g : X) * y * (g : X)⁻¹ = b := by
      rw [← hby]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    rw [heq]
    exact Subgroup.mem_subgroupOf.mp hb
  have hy2 : orderOf (y : X) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_two_of_isInvolution hyinv
  have hye := hc.eq_of_conj_mem hgY (Subgroup.mem_subgroupOf.mp hyB) hgy hy2
  exact heW (hye ▸ y.property)

variable (hc : BaseConfig Y e) {L : Subgroup X} (hL : CFSG.IsComponent L) (heL : e ∉ L)
include hc hL heL

theorem component_two_le_pRank : 2 ≤ CFSG.Open.pRank 2 L :=
  component_two_le_pRank_of_not_mem hc.oddCore_eq_bot hc.center hc.order hc.mem_pCore
    hc.pCore_pRank hL heL

theorem component_characteristic : L.Characteristic := by
  obtain ⟨P, hPY, hcore⟩ := hc.sylow
  exact proper_full_core_high_rank_component_characteristic P Y hc.ne_top hPY hcore L
    ((CFSG.isComponent_iff_open L).mp hL) (hc.component_two_le_pRank hL heL)

theorem component_normal : L.Normal := by
  have := hc.component_characteristic hL heL
  infer_instance

theorem component_not_le : ¬ L ≤ Y := by
  obtain ⟨P, hPY, hcore⟩ := hc.sylow
  have := hc.component_normal hL heL
  exact normal_rank_two_not_le_overgroup P Y hc.ne_top hPY hcore L
    (hc.component_two_le_pRank hL heL)

theorem involution_mem_component_or {t : X} (ht : orderOf t = 2) : t ∈ L ∨ e * t ∈ L := by
  by_contra hcon
  push Not at hcon
  obtain ⟨htL, hetL⟩ := hcon
  have hnormal := hc.component_normal hL heL
  obtain ⟨g, hsY⟩ := hc.exists_conj_mem ht
  set s := g⁻¹ * t * g with hs
  have hs2 : orderOf s = 2 := (orderOf_inv_mul_mul g t).trans ht
  have hsL : s ∉ L := by
    intro h
    apply htL
    have := hnormal.conj_mem s h g
    rwa [hs, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
  have hesL : e * s ∉ L := by
    intro h
    apply hetL
    have := hnormal.conj_mem _ h g
    rwa [hs, show g * (e * (g⁻¹ * t * g)) * g⁻¹ = (g * e * g⁻¹) * t by group,
      (hc.commute_center g).eq, mul_inv_cancel_right] at this
  set W := L ⊔ Subgroup.zpowers s with hW
  have hsW : s ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have heW : e ∉ W := by
    intro hmem
    obtain ⟨j, hj, k, hk, hjk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rcases eq_one_or_eq_of_mem_zpowers hs2 hk with rfl | rfl
    · rw [mul_one] at hjk
      exact heL (hjk ▸ hj)
    · apply hesL
      rwa [← hjk, mul_assoc, mul_self_eq_one_of_orderOf_eq_two hs2, mul_one]
  have hWY : ¬ W ≤ Y := fun h => hc.component_not_le hL heL (le_sup_left.trans h)
  have hB := hc.isStronglyEmbedded_subgroupOf heW hWY hsW hsY hs2
  obtain ⟨a, haL, -, -, ha2, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hc.component_two_le_pRank hL heL)
  obtain ⟨c, -, hc'⟩ := TheoremC.exists_conj_of_isStronglyEmbedded hB
    (Subgroup.mem_sup_left haL : a ∈ W) hsW ha2 hs2
  apply hsL
  rw [← hc']
  simpa using hnormal.conj_mem a haL c⁻¹

theorem involution_mem_component_sup {t : X} (ht : orderOf t = 2) :
    t ∈ L ⊔ Subgroup.zpowers e := by
  rcases hc.involution_mem_component_or hL heL ht with htL | hetL
  · exact Subgroup.mem_sup_left htL
  · have : t = e * (e * t) := by rw [← mul_assoc, hc.mul_self, one_mul]
    rw [this]
    exact (L ⊔ Subgroup.zpowers e).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
      (Subgroup.mem_sup_left hetL)

theorem mul_self_ne_of_mem_component_sup {x : X} (hx : x ∈ L ⊔ Subgroup.zpowers e) :
    x * x ≠ e := by
  have hnormal := hc.component_normal hL heL
  obtain ⟨l, hl, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
  intro hsq
  apply heL
  have hkk : l * k * (l * k) = l * l := by
    rcases eq_one_or_eq_of_mem_zpowers hc.order hk with hk1 | hke
    · rw [hk1, mul_one]
    · rw [hke, mul_assoc l e, ← mul_assoc e l e, ← (hc.commute_center l).eq, mul_assoc l e e,
        hc.mul_self, mul_one]
  rw [hkk] at hsq
  exact hsq ▸ L.mul_mem hl hl

end BaseConfig

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
