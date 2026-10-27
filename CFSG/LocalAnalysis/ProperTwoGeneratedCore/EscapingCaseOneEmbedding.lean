module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

theorem isInvolution_of_orderOf_eq_two {K : Type*} [Group K] {a : K} (ha : orderOf a = 2) :
    IsInvolution a :=
  ⟨fun h => by rw [h, orderOf_one] at ha; exact absurd ha (by decide),
    by rw [← ha, pow_orderOf_eq_one]⟩

theorem orderOf_eq_two_of_isInvolution {K : Type*} [Group K] {a : K} (ha : IsInvolution a) :
    orderOf a = 2 :=
  orderOf_eq_prime ha.2 ha.1

theorem mul_self_eq_one_of_orderOf_eq_two {K : Type*} [Group K] {a : K} (ha : orderOf a = 2) :
    a * a = 1 := by
  have h := pow_orderOf_eq_one a
  rwa [ha, pow_two] at h

theorem orderOf_inv_mul_mul {K : Type*} [Group K] (g a : K) :
    orderOf (g⁻¹ * a * g) = orderOf a := by
  simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj g⁻¹).orderOf_eq a

theorem eq_one_or_eq_of_mem_zpowers {K : Type*} [Group K] {a b : K} (ha : orderOf a = 2)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

namespace EscapingQuotientData

theorem isStronglyEmbedded_subgroupOf (hq : EscapingQuotientData H x)
    {Y : Subgroup (EscapingQuotient x)} (hxY : escapingBar x ∉ Y)
    (hYH : ¬ Y ≤ escapingImage H x) {t : EscapingQuotient x} (htY : t ∈ Y)
    (htH : t ∈ escapingImage H x) (ht : orderOf t = 2) :
    BenderSuzuki.IsStronglyEmbedded ((escapingImage H x).subgroupOf Y) := by
  refine ⟨fun htop => hYH (Subgroup.subgroupOf_eq_top.mp htop),
    ⟨⟨t, htY⟩, Subgroup.mem_subgroupOf.mpr htH,
      isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ht])⟩, ?_⟩
  intro g hg y hyB hyconj hyinv
  have hgH : (g : EscapingQuotient x) ∉ escapingImage H x :=
    fun h => hg (Subgroup.mem_subgroupOf.mpr h)
  obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hyconj
  have hgy : (g : EscapingQuotient x) * y * (g : EscapingQuotient x)⁻¹ ∈ escapingImage H x := by
    have heq : (g : EscapingQuotient x) * y * (g : EscapingQuotient x)⁻¹ = b := by
      rw [← hby]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul,
        Subgroup.coe_inv]
      group
    rw [heq]
    exact Subgroup.mem_subgroupOf.mp hb
  have hy2 : orderOf (y : EscapingQuotient x) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_two_of_isInvolution hyinv
  have hyx := hq.eq_bar_of_conj_mem hgH (Subgroup.mem_subgroupOf.mp hyB) hgy hy2
  exact hxY (hyx ▸ y.property)

theorem exists_conj_of_isStronglyEmbedded {Y : Subgroup (EscapingQuotient x)}
    (hB : BenderSuzuki.IsStronglyEmbedded ((escapingImage H x).subgroupOf Y))
    {a b : EscapingQuotient x}
    (haY : a ∈ Y) (hbY : b ∈ Y) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ c ∈ Y, c⁻¹ * a * c = b := by
  obtain ⟨g, hg⟩ := hB.involutions_conjugate (x := ⟨a, haY⟩) (y := ⟨b, hbY⟩)
    (isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, ha]))
    (isInvolution_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hb]))
  exact ⟨g, g.property, congrArg Subtype.val hg⟩

theorem exists_conj_mem_image (hq : EscapingQuotientData H x) {t : EscapingQuotient x}
    (ht : orderOf t = 2) : ∃ g : EscapingQuotient x, g⁻¹ * t * g ∈ escapingImage H x := by
  obtain ⟨U, hUH, -⟩ := hq.sylow
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow U (isPGroup_zpowers_of_orderOf_eq_two ht)
  exact ⟨g, hUH (hg t (Subgroup.mem_zpowers t))⟩

variable (hq : EscapingQuotientData H x) {J : Subgroup (EscapingQuotient x)}
  (hJ : CFSG.IsComponent J) (hxJ : escapingBar x ∉ J)
include hq hJ hxJ

theorem component_exists_involution_mem_image :
    ∃ t ∈ J, t ∈ escapingImage H x ∧ orderOf t = 2 := by
  obtain ⟨a, haJ, -, -, ha2, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hq.component_two_le_pRank hJ hxJ)
  obtain ⟨g, hg⟩ := hq.exists_conj_mem_image ha2
  have hnormal := hq.component_normal hJ hxJ
  exact ⟨g⁻¹ * a * g, by simpa using hnormal.conj_mem a haJ g⁻¹, hg,
    (orderOf_inv_mul_mul g a).trans ha2⟩

theorem component_isStronglyEmbedded :
    BenderSuzuki.IsStronglyEmbedded ((escapingImage H x).subgroupOf J) := by
  obtain ⟨t, htJ, htH, ht⟩ := hq.component_exists_involution_mem_image hJ hxJ
  exact hq.isStronglyEmbedded_subgroupOf hxJ (hq.component_not_le_image hJ hxJ) htJ htH ht

theorem component_conj {a b : EscapingQuotient x} (haJ : a ∈ J) (hbJ : b ∈ J)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : ∃ c ∈ J, c⁻¹ * a * c = b :=
  exists_conj_of_isStronglyEmbedded (hq.component_isStronglyEmbedded hJ hxJ) haJ hbJ ha hb

theorem involution_mem_component_or {t : EscapingQuotient x} (ht : orderOf t = 2) :
    t ∈ J ∨ escapingBar x * t ∈ J := by
  by_contra hcon
  push Not at hcon
  obtain ⟨htJ, hxtJ⟩ := hcon
  have hnormal := hq.component_normal hJ hxJ
  obtain ⟨g, hsH⟩ := hq.exists_conj_mem_image ht
  set s := g⁻¹ * t * g with hs
  have hs2 : orderOf s = 2 := (orderOf_inv_mul_mul g t).trans ht
  have hsJ : s ∉ J := by
    intro h
    apply htJ
    have := hnormal.conj_mem s h g
    rwa [hs, show g * (g⁻¹ * t * g) * g⁻¹ = t by group] at this
  have hxsJ : escapingBar x * s ∉ J := by
    intro h
    apply hxtJ
    have := hnormal.conj_mem _ h g
    rwa [hs, show g * (escapingBar x * (g⁻¹ * t * g)) * g⁻¹ =
      (g * escapingBar x * g⁻¹) * t by group, (hq.commute_bar g).eq, mul_inv_cancel_right]
      at this
  set Y := J ⊔ Subgroup.zpowers s with hY
  have hsY : s ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hxY : escapingBar x ∉ Y := by
    intro hmem
    obtain ⟨j, hj, k, hk, hjk⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    rcases eq_one_or_eq_of_mem_zpowers hs2 hk with rfl | rfl
    · rw [mul_one] at hjk
      exact hxJ (hjk ▸ hj)
    · apply hxsJ
      rwa [← hjk, mul_assoc, mul_self_eq_one_of_orderOf_eq_two hs2, mul_one]
  have hYH : ¬ Y ≤ escapingImage H x :=
    fun h => hq.component_not_le_image hJ hxJ (le_sup_left.trans h)
  have hB := hq.isStronglyEmbedded_subgroupOf hxY hYH hsY hsH hs2
  obtain ⟨a, haJ, -, -, ha2, -⟩ :=
    exists_commuting_involutions_of_two_le_pRank (hq.component_two_le_pRank hJ hxJ)
  obtain ⟨c, -, hc⟩ := exists_conj_of_isStronglyEmbedded hB
    (Subgroup.mem_sup_left haJ : a ∈ Y) hsY ha2 hs2
  apply hsJ
  rw [← hc]
  simpa using hnormal.conj_mem a haJ c⁻¹

end EscapingQuotientData

end CFSG.ProperTwoGeneratedCore.Assembly
