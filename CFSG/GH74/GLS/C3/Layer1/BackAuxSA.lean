module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup

theorem exists_normalizer_sq_mem_of_lt_top {W : Type*} [Group W] [Finite W] (hW : IsPGroup 2 W)
    {H : Subgroup W} (hH : H < ⊤) :
    ∃ a ∈ normalizer (H : Set W), a ∉ H ∧ a ^ 2 ∈ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent W := hW.isNilpotent
  have hlt : H < normalizer (H : Set W) := Group.normalizerCondition_of_isNilpotent H hH
  have hQ : IsPGroup 2 (↥(normalizer (H : Set W)) ⧸ H.subgroupOf (normalizer (H : Set W))) :=
    (hW.to_subgroup (normalizer (H : Set W))).to_quotient _
  have hne : Nat.card (↥(normalizer (H : Set W)) ⧸ H.subgroupOf (normalizer (H : Set W))) ≠ 1 := by
    rw [← Subgroup.index_eq_card, Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
    exact not_le_of_gt hlt
  have hdvd := hQ.card_eq_or_dvd.resolve_left hne
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  rw [orderOf_eq_prime_iff] at hx
  obtain ⟨hx2, hx1⟩ := hx
  refine ⟨(n : W), n.2, ?_, ?_⟩
  · intro hn
    exact hx1 ((QuotientGroup.eq_one_iff n).mpr hn)
  · have : n ^ 2 ∈ H.subgroupOf (normalizer (H : Set W)) := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hx2
    exact this

theorem exists_sylow_gt_and_a {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hnot : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ T < S ∧
      ∃ a ∈ S, a ∈ Subgroup.normalizer (T : Set G) ∧ a ∉ T ∧ a ^ 2 ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (P : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hlt : T < (P : Subgroup G) := by
    refine lt_of_le_of_ne hTP ?_
    intro h
    exact hnot (h ▸ hS)
  have hH : T.subgroupOf (P : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    exact not_le_of_gt hlt (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨a, ha, haT, ha2⟩ := exists_normalizer_sq_mem_of_lt_top P.isPGroup' hH
  rw [← Subgroup.subgroupOf_normalizer_eq hTP] at ha
  exact ⟨P, hS, hlt, (a : G), a.2, ha, haT, ha2⟩

end CFSG.GH74.GLS.C3.Layer1.Back
