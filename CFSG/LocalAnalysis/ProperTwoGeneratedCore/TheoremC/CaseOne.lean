module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.CaseOneComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.Statement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_of_isStronglyEmbedded {W : Subgroup X} {M : Subgroup W}
    (hM : BenderSuzuki.IsStronglyEmbedded M) {a b : X} (haW : a ∈ W) (hbW : b ∈ W)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : ∃ c ∈ W, c⁻¹ * a * c = b := by
  obtain ⟨g, hg⟩ := hM.involutions_conjugate (x := ⟨a, haW⟩) (y := ⟨b, hbW⟩)
    (isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ha]))
    (isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hb]))
  exact ⟨g, g.property, congrArg Subtype.val hg⟩

namespace CoreConfig

variable {Y : Subgroup X} {u z : X}

theorem isStronglyEmbedded_subgroupOf (hc : CoreConfig Y u z) {W : Subgroup X} (huW : u ∉ W)
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
  have hyu := hc.eq_of_conj_mem hgY (Subgroup.mem_subgroupOf.mp hyB) hgy hy2
  exact huW (hyu ▸ y.property)

theorem exists_conj_mem (hc : CoreConfig Y u z) {t : X} (ht : orderOf t = 2) :
    ∃ g : X, g⁻¹ * t * g ∈ Y := by
  obtain ⟨P, hPY, -, -, -⟩ := hc.sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P (isPGroup_zpowers_of_orderOf_eq_two ht)
  exact ⟨g, hPY (hg t (Subgroup.mem_zpowers t))⟩

variable (hc : CoreConfig Y u z) {J : Subgroup X} (hJ : CFSG.IsComponent J) (huJ : u ∉ J)
include hc hJ huJ

theorem component_exists_involution_mem : ∃ t ∈ J, t ∈ Y ∧ orderOf t = 2 := by
  obtain ⟨a, haJ, -, -, ha2, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hc.component_two_le_pRank hJ huJ)
  obtain ⟨g, hg⟩ := hc.exists_conj_mem ha2
  have hnormal := hc.component_normal hJ huJ
  exact ⟨g⁻¹ * a * g, by simpa using hnormal.conj_mem a haJ g⁻¹, hg,
    (orderOf_inv_mul_mul g a).trans ha2⟩

theorem component_isStronglyEmbedded : BenderSuzuki.IsStronglyEmbedded (Y.subgroupOf J) := by
  obtain ⟨t, htJ, htY, ht⟩ := hc.component_exists_involution_mem hJ huJ
  exact hc.isStronglyEmbedded_subgroupOf huJ (hc.component_not_le hJ huJ) htJ htY ht

theorem involution_mem_component_or {t : X} (ht : orderOf t = 2) : t ∈ J ∨ u * t ∈ J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨htJ, hutJ⟩ := hcon
  have hnormal := hc.component_normal hJ huJ
  obtain ⟨g, hsY⟩ := hc.exists_conj_mem ht
  set s := g⁻¹ * t * g with hs
  have hs2 : orderOf s = 2 := (orderOf_inv_mul_mul g t).trans ht
  have hsJ : s ∉ J := by
    intro h
    apply htJ
    have := hnormal.conj_mem s h g
    rwa [hs, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
  have husJ : u * s ∉ J := by
    intro h
    apply hutJ
    have := hnormal.conj_mem _ h g
    rwa [hs, show g * (u * (g⁻¹ * t * g)) * g⁻¹ = (g * u * g⁻¹) * t by group,
      (hc.commute_center g).eq, mul_inv_cancel_right] at this
  set W := J ⊔ Subgroup.zpowers s with hW
  have hsW : s ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have huW : u ∉ W := by
    intro hmem
    obtain ⟨j, hj, k, hk, hjk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rcases eq_one_or_eq_of_mem_zpowers hs2 hk with rfl | rfl
    · rw [mul_one] at hjk
      exact huJ (hjk ▸ hj)
    · apply husJ
      rwa [← hjk, mul_assoc, mul_self_eq_one_of_orderOf_eq_two hs2, mul_one]
  have hWY : ¬ W ≤ Y := fun h => hc.component_not_le hJ huJ (le_sup_left.trans h)
  have hB := hc.isStronglyEmbedded_subgroupOf huW hWY hsW hsY hs2
  obtain ⟨a, haJ, -, -, ha2, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hc.component_two_le_pRank hJ huJ)
  obtain ⟨c, -, hc'⟩ := exists_conj_of_isStronglyEmbedded hB
    (Subgroup.mem_sup_left haJ : a ∈ W) hsW ha2 hs2
  apply hsJ
  rw [← hc']
  simpa using hnormal.conj_mem a haJ c⁻¹

end CoreConfig

theorem caseOneInvolutions : CaseOneInvolutions := by
  intro X _ _ Y u z hc J hJ huJ
  exact ⟨hc.component_isSimpleGroup hJ huJ, hc.component_normal hJ huJ,
    fun _ ht => hc.involution_mem_component_or hJ huJ ht⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
