module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionMaximalPrimeClass
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullConjugacy
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

theorem elementary_four_exists_involution_ne (V : Subgroup G)
    (hV : IsElemAbelian 2 V) (hcard : Nat.card V = 4) (a : G) :
    ∃ v : G, v ∈ V ∧ orderOf v = 2 ∧ v ≠ a := by
  obtain ⟨v, hvone, hva⟩ : ∃ v : V, (v : G) ≠ 1 ∧ (v : G) ≠ a := by
    by_contra hnone
    push Not at hnone
    have hcases : ∀ v : V, (v : G) = 1 ∨ (v : G) = a := by
      intro v
      by_cases hv : (v : G) = 1
      · exact Or.inl hv
      · exact Or.inr (hnone v hv)
    let f : V → ({(1 : G), a} : Set G) := fun v => ⟨v, hcases v⟩
    have hf : Function.Injective f := by
      intro v w heq
      exact Subtype.ext (congrArg
        (fun x : ({(1 : G), a} : Set G) => (x : G)) heq)
    have htwo : Nat.card ({(1 : G), a} : Set G) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      by_cases ha : a = 1
      · simp [ha]
      · exact (Set.ncard_pair (Ne.symm ha)).le
    have hbound := (Nat.card_le_card_of_injective f hf).trans htwo
    rw [hcard] at hbound
    omega
  exact ⟨v, v.property, orderOf_eq_prime_iff.mpr ⟨hV.2 v v.property, hvone⟩, hva⟩

theorem two_group_rank_two_involution_has_commuting_partner
    (hG : IsPGroup 2 G) (hrank : 2 ≤ twoRank G)
    (a : G) (ha : orderOf a = 2) :
    ∃ b : G, orderOf b = 2 ∧ b ≠ a ∧ Commute a b := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial G := nontrivial_of_ne a 1 (orderOf_eq_prime_iff.mp ha).2
  let : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hcenterEven : 2 ∣ Nat.card (Subgroup.center G) :=
    (hG.to_subgroup (Subgroup.center G)).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt (Finite.one_lt_card : 1 < Nat.card (Subgroup.center G)))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hcenterEven
  have hcG : orderOf (c : G) = 2 := (Subgroup.orderOf_coe c).trans hc
  by_cases hca : (c : G) = a
  · have haCenter : a ∈ Subgroup.center G := hca ▸ c.property
    have hfour : ∃ V : Subgroup G, IsElemAbelian 2 V ∧ Nat.card V = 4 := by
      by_contra hno
      push Not at hno
      have hbound := twoRank_le_one_of_no_four_group hno
      omega
    obtain ⟨V, hV, hcard⟩ := hfour
    obtain ⟨b, _hbV, hb, hba⟩ := elementary_four_exists_involution_ne V hV hcard a
    exact ⟨b, hb, hba, (Subgroup.mem_center_iff.mp haCenter b).symm⟩
  · exact ⟨c, hcG, hca, Subgroup.mem_center_iff.mp c.property a⟩

theorem two_group_rank_two_involution_in_four_group
    (hG : IsPGroup 2 G) (hrank : 2 ≤ twoRank G)
    (a : G) (ha : orderOf a = 2) :
    ∃ b : G, orderOf b = 2 ∧ b ≠ a ∧ Commute a b ∧
      IsElemAbelian 2 (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ∧
      Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) = 4 := by
  obtain ⟨b, hb, hba, hab⟩ :=
    two_group_rank_two_involution_has_commuting_partner hG hrank a ha
  obtain ⟨helem, hcard, _⟩ := commuting_distinct_involutions_four_group ha hb hab hba
  exact ⟨b, hb, hba, hab, helem, hcard⟩

@[expose, instance_reducible] def pointRootConjugationAction
    (H W : Subgroup G) (hWH : W ≤ H) (z : G) :
    MulAction W (conjugacyWithin H z) where
  smul w x := ⟨(w : G) * x * (w : G)⁻¹, by
    obtain ⟨a, ha⟩ := x.property
    refine ⟨a * (⟨(w : G)⁻¹, H.inv_mem (hWH w.property)⟩ : H), ?_⟩
    change ((a : G) * (w : G)⁻¹)⁻¹ * z * ((a : G) * (w : G)⁻¹) =
      (w : G) * x * (w : G)⁻¹
    rw [← ha]
    group⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : G) * x * (1 : G)⁻¹ = x
    simp only [inv_one, one_mul, mul_one]
  mul_smul w v x := by
    apply Subtype.ext
    change ((w : G) * v) * x * ((w : G) * v)⁻¹ =
      (w : G) * ((v : G) * x * (v : G)⁻¹) * (w : G)⁻¹
    group

theorem original_two_subgroup_has_common_point_root
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (W : Subgroup G) (hWH : W ≤ H) (hW : IsPGroup 2 W) :
    ∃ z₀ : G, z₀ ∈ conjugacyWithin H z ∧
      z₀ ∈ Subgroup.centralizer (W : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction W (conjugacyWithin H z) := pointRootConjugationAction H W hWH z
  have hodd := point_subgroup_full_class_card_odd h S hzS hzcenter
  obtain ⟨x, hx⟩ := hW.nonempty_fixed_point_of_prime_not_dvd_card
    (conjugacyWithin H z) hodd.not_two_dvd_nat
  refine ⟨x, x.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro w hw
  have hf := congrArg (fun y : conjugacyWithin H z => (y : G))
    (MulAction.mem_fixedPoints.mp hx (⟨w, hw⟩ : W))
  change w * (x : G) * w⁻¹ = x at hf
  exact mul_inv_eq_iff_eq_mul.mp hf

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
