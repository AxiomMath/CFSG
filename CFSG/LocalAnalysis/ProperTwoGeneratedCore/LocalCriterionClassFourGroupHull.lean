module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCoreCover
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCountingInheritance

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.TwoRankLowerBound.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G] [Finite G]

theorem involution_hull_rank_le_one_isolated {z : G} (hz : orderOf z = 2)
    (hrank : twoRank (involutionPointHull z) ≤ 1) :
    ∀ g : G, Commute (g⁻¹ * z * g) z → g⁻¹ * z * g = z := by
  let L := involutionPointHull z
  have hzL : z ∈ L := Subgroup.subset_closure (distinguished_mem_pointClass z)
  intro g hcommute
  have hconjugateL : g⁻¹ * z * g ∈ L := Subgroup.subset_closure ⟨g, rfl⟩
  have hconjugateOrder : orderOf (g⁻¹ * z * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq z).trans hz
  have hcommuteL : Commute (⟨g⁻¹ * z * g, hconjugateL⟩ : L) (⟨z, hzL⟩ : L) := by
    apply Subtype.ext
    exact hcommute.eq
  exact congrArg Subtype.val (commuting_involutions_eq_of_twoRank_le_one L hrank
    ⟨g⁻¹ * z * g, hconjugateL⟩ ⟨z, hzL⟩
    ((Subgroup.orderOf_coe _).symm.trans hconjugateOrder)
    ((Subgroup.orderOf_coe _).symm.trans hz) hcommuteL)

theorem local_involution_hull_two_rank_of_commuting_class
    {H : Subgroup G} {z w : G} (h : InvolutionPointLocalEmbedding H z)
    (Y : Subgroup G) (hzY : z ∈ Y) (hescapeY : ¬ Y ≤ H)
    (hwY : w ∈ Y) (hwclass : w ∈ involutionPointClass z)
    (hcommute : Commute z w) (hne : w ≠ z) :
    2 ≤ twoRank (involutionPointHull (⟨z, hzY⟩ : Y)) := by
  by_contra hrank
  let zY : Y := ⟨z, hzY⟩
  change ¬ 2 ≤ twoRank (involutionPointHull zY) at hrank
  have hzYorder : orderOf zY = 2 :=
    (Subgroup.orderOf_coe zY).symm.trans h.distinguished_order
  have hsmall : twoRank (involutionPointHull zY) ≤ 1 := by omega
  have hisolated := involution_hull_rank_le_one_isolated hzYorder hsmall
  obtain ⟨_, hfactor⟩ := native_zStar_of_isolated_involution hzYorder hisolated
  let R : Subgroup G := (CFSG.oddCore Y).map Y.subtype
  have hRodd : Odd (Nat.card R) := by
    rw [Subgroup.card_subtype]
    exact CFSG.ComponentClassification.OddCore.odd_card Y
  have hYnormalizes : Y ≤ Subgroup.normalizer (R : Set G) := by
    simpa only [Subgroup.normalizer_eq_top, Subgroup.map_top, Subgroup.subtype_range]
      using (Subgroup.le_normalizer_map (H := CFSG.oddCore Y) Y.subtype)
  have hpairNormalizes : Subgroup.zpowers z ⊔ Subgroup.zpowers w ≤
      Subgroup.normalizer (R : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr (hYnormalizes hzY))
      (Subgroup.zpowers_le.mpr (hYnormalizes hwY))
  have hRH : R ≤ H := local_point_odd_subgroup_le_of_commuting_class
    h hwclass hcommute hne R hRodd hpairNormalizes
  apply hescapeY
  intro y hy
  obtain ⟨c, hc, x, hx, heq⟩ := hfactor (⟨y, hy⟩ : Y)
  have hcG : (c : G) ∈ Subgroup.centralizer ({z} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hxG : (x : G) ∈ R := Subgroup.mem_map_of_mem Y.subtype hx
  have heqG : y = (c : G) * (x : G) := congrArg Subtype.val heq
  rw [heqG]
  exact H.mul_mem (point_centralizer_le h hcG) (hRH hxG)

theorem local_class_four_group_hull_central_sylow_and_rank
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hzY : z ∈ Y) (hescapeY : ¬ Y ≤ H)
    (A : Subgroup G) (hAY : A ≤ Y) (hA : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 4) (hzA : z ∈ A)
    (hclass : ∀ a ∈ A, a ≠ 1 → a ∈ involutionPointClass z) :
    ∃ (T : Sylow 2 Y) (hzT : (⟨z, hzY⟩ : Y) ∈ (T : Subgroup Y)),
      (⟨(⟨z, hzY⟩ : Y), hzT⟩ : (T : Subgroup Y)) ∈
        Subgroup.center (T : Subgroup Y) ∧
      2 ≤ twoRank (involutionPointHull (⟨z, hzY⟩ : Y)) := by
  obtain ⟨_, hcentralSylow⟩ := involution_point_subgroup_inheritance h Y hzY hescapeY
  obtain ⟨T, hzT, hzcenterT⟩ := hcentralSylow ⟨S, hzS, hzcenter⟩
  have hnotle : ¬ A ≤ Subgroup.zpowers z := by
    intro hle
    have hbound := Subgroup.card_le_of_le hle
    rw [hAcard, Nat.card_zpowers, h.distinguished_order] at hbound
    omega
  obtain ⟨w, hwA, hwZ⟩ := IsConcreteLE.not_le_iff_exists.mp hnotle
  have hwone : w ≠ 1 := fun heq => hwZ (heq ▸ (Subgroup.zpowers z).one_mem)
  have hwz : w ≠ z := fun heq => hwZ (heq ▸ Subgroup.mem_zpowers z)
  have hcommute : Commute z w := by
    exact (congrArg Subtype.val
      (@mul_comm' A _ hA.1 (⟨z, hzA⟩ : A) (⟨w, hwA⟩ : A)))
  exact ⟨T, hzT, hzcenterT, local_involution_hull_two_rank_of_commuting_class
    h Y hzY hescapeY (hAY hwA) (hclass w hwA hwone) hcommute hwz⟩

theorem involution_point_class_four_group_hull_rank
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (Y : Subgroup G) (hzY : z ∈ Y) (hescapeY : ¬ Y ≤ H)
    (A : Subgroup G) (hAY : A ≤ Y) (hA : IsElemAbelian 2 A)
    (hAcard : Nat.card A = 4) (hzA : z ∈ A)
    (hclass : ∀ a ∈ A, a ≠ 1 → a ∈ involutionPointClass z) :
    2 ≤ twoRank (involutionPointHull (⟨z, hzY⟩ : Y)) := by
  obtain ⟨T, hzT, _, hrank⟩ := local_class_four_group_hull_central_sylow_and_rank
    h S hzS hzcenter Y hzY hescapeY A hAY hA hAcard hzA hclass
  exact hrank

end CFSG.ProperTwoGeneratedCore
