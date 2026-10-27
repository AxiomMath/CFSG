module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapOrbits
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairSwapFusion

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

theorem unique_rank_one_pair_stabilizer_two_swap_orbits_ambient
    (K D : Subgroup G) (hDK : D ≤ K) [(D.subgroupOf K).Normal]
    (J : Subgroup K) [J.Normal]
    (hDindex : (D.subgroupOf K).index = 2)
    (hJodd : Odd (Nat.card J)) (hJD : J ≤ D.subgroupOf K)
    (hfour : ¬ TwoRankAtLeastTwo (D.subgroupOf K))
    (u t : G) (hu : IsInvolution u) (ht : IsInvolution t)
    (huD : u ∈ D) (htK : t ∈ K) (htD : t ∉ D) (hut : Commute u t)
    (htcentral : QuotientGroup.mk' J (⟨t, htK⟩ : K) ∈ Subgroup.center (K ⧸ J))
    (hclasses : ∀ s : G, IsInvolution s →
      s ∈ conjugacyWithin (⊤ : Subgroup G) u ∨ s ∈ conjugacyWithin (⊤ : Subgroup G) t)
    (hclassesDistinct : conjugacyWithin (⊤ : Subgroup G) u ≠
      conjugacyWithin (⊤ : Subgroup G) t)
    (htfiber : conjugacyWithin (⊤ : Subgroup G) t ∩ ((K : Set G) \ (D : Set G)) =
      conjugacyWithin D t) :
    {s : G | IsInvolution s ∧ s ∈ K ∧ s ∉ D} =
        conjugacyWithin D t ∪ conjugacyWithin D (u * t) ∧
      Disjoint (conjugacyWithin D t) (conjugacyWithin D (u * t)) ∧
      Nat.card (conjugacyWithin D t) =
        ((Subgroup.centralizer ({t} : Set G)).subgroupOf D).index ∧
      Nat.card (conjugacyWithin D (u * t)) =
        ((Subgroup.centralizer ({u * t} : Set G)).subgroupOf D).index ∧
      conjugacyWithin (⊤ : Subgroup G) u ∩ ((K : Set G) \ (D : Set G)) =
        conjugacyWithin D (u * t) ∧
      u * t ∈ conjugacyWithin (⊤ : Subgroup G) u := by
  let uK : K := ⟨u, hDK huD⟩
  let tK : K := ⟨t, htK⟩
  have huI : IsInvolution uK := (isInvolution_coe_iff K uK).mp hu
  have htI : IsInvolution tK := (isInvolution_coe_iff K tK).mp ht
  have hutK : Commute uK tK := Commute.of_map K.subtype_injective hut
  have hlocalK := unique_rank_one_pair_stabilizer_two_swap_orbits (D.subgroupOf K) J
    hDindex hJodd hJD hfour uK tK huI htI huD htD hutK htcentral
  have himage : K.subtype '' {s : K | IsInvolution s ∧ s ∉ D.subgroupOf K} =
      {s : G | IsInvolution s ∧ s ∈ K ∧ s ∉ D} := by
    apply Set.Subset.antisymm
    · rintro x ⟨s, ⟨hsI, hsD⟩, rfl⟩
      exact ⟨(isInvolution_coe_iff K s).mpr hsI, s.property, hsD⟩
    · rintro x ⟨hxI, hxK, hxD⟩
      exact ⟨⟨x, hxK⟩, ⟨(isInvolution_coe_iff K ⟨x, hxK⟩).mp hxI, hxD⟩, rfl⟩
  have hlocal : {s : G | IsInvolution s ∧ s ∈ K ∧ s ∉ D} =
      conjugacyWithin D t ∪ conjugacyWithin D (u * t) := by
    calc
      {s : G | IsInvolution s ∧ s ∈ K ∧ s ∉ D} =
          K.subtype '' {s : K | IsInvolution s ∧ s ∉ D.subgroupOf K} := himage.symm
      _ = K.subtype '' (conjugacyWithin (D.subgroupOf K) tK ∪
          conjugacyWithin (D.subgroupOf K) (uK * tK)) := by rw [hlocalK.1]
      _ = K.subtype '' conjugacyWithin (D.subgroupOf K) tK ∪
          K.subtype '' conjugacyWithin (D.subgroupOf K) (uK * tK) :=
        Set.image_union _ _ _
      _ = conjugacyWithin D t ∪ conjugacyWithin D (u * t) := by
        rw [conjugacyWithin_subgroupOf_image K D hDK tK,
          conjugacyWithin_subgroupOf_image K D hDK (uK * tK)]
        rfl
  have hdisj : Disjoint (conjugacyWithin D t) (conjugacyWithin D (u * t)) := by
    have h := Set.disjoint_image_of_injective K.subtype_injective hlocalK.2.1
    rw [conjugacyWithin_subgroupOf_image K D hDK tK,
      conjugacyWithin_subgroupOf_image K D hDK (uK * tK)] at h
    exact h
  have hfusion := ambient_fusion_of_two_swap_orbits K D u t hu hlocal hdisj
    hclasses hclassesDistinct htfiber
  exact ⟨hlocal, hdisj,
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.conjugacyWithin_card_eq_centralizer_index D t,
    CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow.conjugacyWithin_card_eq_centralizer_index D (u * t),
    hfusion.1, hfusion.2⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
