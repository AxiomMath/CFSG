module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryZStarFactorization
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u v

variable {G : Type u} [Group G]

@[expose] def subgroupRightCosetInclusion (H A : Subgroup G) :
    rightCosetSpace (H.subgroupOf A) → rightCosetSpace H :=
  Quotient.map' A.subtype (by
    intro a b hab
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    exact hab)

theorem subgroupRightCosetInclusion_mk (H A : Subgroup G) (a : A) :
    subgroupRightCosetInclusion H A (rightCosetMk (H.subgroupOf A) a) =
      rightCosetMk H (a : G) := rfl

theorem subgroupRightCosetInclusion_injective (H A : Subgroup G) :
    Function.Injective (subgroupRightCosetInclusion H A) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  apply Quotient.sound
  have hrel : QuotientGroup.rightRel H (a : G) (b : G) := Quotient.exact hab
  change QuotientGroup.rightRel (H.subgroupOf A) a b
  rw [QuotientGroup.rightRel_apply] at hrel ⊢
  exact hrel

theorem subgroupRightCosetInclusion_translate (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (a : A) :
    subgroupRightCosetInclusion H A (rightCosetTranslate (H.subgroupOf A) beta a) =
      rightCosetTranslate H (subgroupRightCosetInclusion H A beta) (a : G) := by
  refine Quotient.inductionOn beta ?_
  intro b
  rfl

theorem subgroupRightCosetInclusion_ne_base (H A : Subgroup G)
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) :
    subgroupRightCosetInclusion H A beta ≠ rightCosetMk H 1 := by
  intro hbase
  apply hbeta
  apply subgroupRightCosetInclusion_injective H A
  simpa only [subgroupRightCosetInclusion_mk, Subgroup.coe_one] using hbase

theorem subgroupRightCosetStabilizer_mem (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (a : A) :
    a ∈ rightCosetStabilizer (H.subgroupOf A) beta ↔
      (a : G) ∈ rightCosetStabilizer H (subgroupRightCosetInclusion H A beta) := by
  rw [mem_rightCosetStabilizer_iff, mem_rightCosetStabilizer_iff]
  constructor
  · intro hfix
    rw [← subgroupRightCosetInclusion_translate, hfix]
  · intro hfix
    apply subgroupRightCosetInclusion_injective H A
    rw [subgroupRightCosetInclusion_translate, hfix]

theorem subgroup_pair_point_stabilizer_map (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) :
    (pairPointStabilizer (H.subgroupOf A) beta).map A.subtype =
      A ⊓ pairPointStabilizer H (subgroupRightCosetInclusion H A beta) := by
  have hmem (a : A) : a ∈ pairPointStabilizer (H.subgroupOf A) beta ↔
      (a : G) ∈ pairPointStabilizer H (subgroupRightCosetInclusion H A beta) := by
    change (a ∈ rightCosetStabilizer (H.subgroupOf A) (rightCosetMk (H.subgroupOf A) 1) ∧
      a ∈ rightCosetStabilizer (H.subgroupOf A) beta) ↔
      ((a : G) ∈ rightCosetStabilizer H (rightCosetMk H 1) ∧
        (a : G) ∈ rightCosetStabilizer H (subgroupRightCosetInclusion H A beta))
    rw [subgroupRightCosetStabilizer_mem, subgroupRightCosetStabilizer_mem,
      subgroupRightCosetInclusion_mk, Subgroup.coe_one]
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.property, (hmem a).mp ha⟩
  · rintro ⟨hxA, hxB⟩
    exact ⟨⟨x, hxA⟩, (hmem ⟨x, hxA⟩).mpr hxB, rfl⟩

theorem subgroup_pair_group_map_le (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) :
    (pairFlipGroup (H.subgroupOf A) beta t).map A.subtype ≤
      pairFlipGroup H (subgroupRightCosetInclusion H A beta) (t : G) := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sup_le
  · intro a ha
    have hg := Subgroup.mem_map_of_mem A.subtype ha
    rw [subgroup_pair_point_stabilizer_map] at hg
    exact pairPointStabilizer_le_pairFlipGroup _ _ _ hg.2
  · exact Subgroup.zpowers_le.mpr (flip_mem_pairFlipGroup _ _ _)

@[expose] def subgroupPairGroupHom (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) :
    pairFlipGroup (H.subgroupOf A) beta t →*
      pairFlipGroup H (subgroupRightCosetInclusion H A beta) (t : G) where
  toFun a := ⟨((a : A) : G), subgroup_pair_group_map_le H A beta t
    (Subgroup.mem_map_of_mem A.subtype a.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem subgroupPairGroupHom_injective (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) :
    Function.Injective (subgroupPairGroupHom H A beta t) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : pairFlipGroup H (subgroupRightCosetInclusion H A beta) (t : G) =>
    (q : G)) hab

theorem subgroup_flip_mem_ambient {H A : Subgroup G} {z : G} (hzA : z ∈ A)
    {beta : rightCosetSpace (H.subgroupOf A)} {t : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    (t : G) ∈ rightPairFlipFiber H z (subgroupRightCosetInclusion H A beta) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := ht.1
    exact ⟨a, congrArg Subtype.val ha⟩
  · have hh := congrArg (subgroupRightCosetInclusion H A) ht.2
    simpa only [subgroupRightCosetInclusion_translate, subgroupRightCosetInclusion_mk,
      Subgroup.coe_one] using hh

@[expose] def subgroupPairOddIntersection (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) : Subgroup A :=
  (pairOddCore H (subgroupRightCosetInclusion H A beta)).subgroupOf A ⊓
    pairFlipGroup (H.subgroupOf A) beta t

theorem subgroup_pair_odd_intersection_map (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) :
    (subgroupPairOddIntersection H A beta t).map A.subtype =
      pairOddCore H (subgroupRightCosetInclusion H A beta) ⊓
        (pairFlipGroup (H.subgroupOf A) beta t).map A.subtype := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha.1, Subgroup.mem_map_of_mem A.subtype ha.2⟩
  · rintro ⟨hxJ, a, haK, hax⟩
    change (a : G) = x at hax
    have haJ : (a : G) ∈ pairOddCore H (subgroupRightCosetInclusion H A beta) := by
      rw [hax]
      exact hxJ
    exact ⟨a, ⟨haJ, haK⟩, hax⟩

theorem subgroup_pair_odd_intersection_comap (H A : Subgroup G)
    (beta : rightCosetSpace (H.subgroupOf A)) (t : A) :
    (((pairOddCore H (subgroupRightCosetInclusion H A beta)).subgroupOf
      (pairFlipGroup H (subgroupRightCosetInclusion H A beta) (t : G))).comap
        (subgroupPairGroupHom H A beta t)).map
          (pairFlipGroup (H.subgroupOf A) beta t).subtype =
      subgroupPairOddIntersection H A beta t := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb, b.property⟩
  · rintro ⟨haJ, haK⟩
    exact ⟨⟨a, haK⟩, haJ, rfl⟩

theorem subgroup_pair_odd_intersection_normal_odd [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) {t : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    ((subgroupPairOddIntersection H A beta t).subgroupOf
      (pairFlipGroup (H.subgroupOf A) beta t)).Normal ∧
        Odd (Nat.card (subgroupPairOddIntersection H A beta t)) := by
  let K := pairFlipGroup H (subgroupRightCosetInclusion H A beta) (t : G)
  let KA := pairFlipGroup (H.subgroupOf A) beta t
  let J := (pairOddCore H (subgroupRightCosetInclusion H A beta)).subgroupOf K
  let f := subgroupPairGroupHom H A beta t
  have hbetag := subgroupRightCosetInclusion_ne_base H A hbeta
  have htG := subgroup_flip_mem_ambient hzA ht
  let : J.Normal := pairOddCore_normal_in_pair_group h.distinguished_order hbetag htG
  have hJodd : Odd (Nat.card J) := by
    change Odd (Nat.card ((pairOddCore H (subgroupRightCosetInclusion H A beta)).subgroupOf K))
    rw [← pair_group_oddCore_subgroupOf_eq h.distinguished_order hbetag htG]
    exact CFSG.ComponentClassification.OddCore.odd_card K
  have hpreodd : Odd (Nat.card (J.comap f)) := hJodd.of_dvd_nat
    (Subgroup.card_comap_dvd_of_injective J f (subgroupPairGroupHom_injective H A beta t))
  have hmap : (J.comap f).map KA.subtype = subgroupPairOddIntersection H A beta t :=
    subgroup_pair_odd_intersection_comap H A beta t
  constructor
  · rw [← hmap]
    have heq : ((J.comap f).map KA.subtype).subgroupOf KA = J.comap f :=
      Subgroup.comap_map_eq_self_of_injective KA.subtype_injective _
    rw [heq]
    infer_instance
  · rw [← hmap, Subgroup.card_subtype]
    exact hpreodd

theorem involution_mem_odd_normal_class {N : Subgroup G} [N.Normal]
    (hodd : Odd (Nat.card N)) {s t : G} (hs : IsInvolution s) (ht : IsInvolution t)
    (hprod : s * t ∈ N) : s ∈ conjugacyWithin N t := by
  let f := QuotientGroup.mk' N
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using ht.sq_eq_one)
  have heq : f s = f t := by
    change (QuotientGroup.mk s : G ⧸ N) = QuotientGroup.mk t
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv, htinv] using hprod
  have hkerodd : Odd (Nat.card f.ker) := by
    change Odd (Nat.card (QuotientGroup.mk' N).ker)
    rwa [QuotientGroup.ker_mk']
  obtain ⟨n, hn, hconj⟩ :=
    CFSG.ProperTwoGeneratedCore.involutions_kernel_conjugate f hkerodd hs ht heq
  have hnN : n ∈ N := by
    change n ∈ (QuotientGroup.mk' N).ker at hn
    rwa [QuotientGroup.ker_mk'] at hn
  refine ⟨⟨n⁻¹, N.inv_mem hnN⟩, ?_⟩
  change n⁻¹⁻¹ * t * n⁻¹ = s
  rw [inv_inv, ← hconj]
  unfold rightConjugateElem
  group

theorem subgroup_pair_flip_product_mem_intersection [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) {t s : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta)
    (hs : s ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    s * t ∈ subgroupPairOddIntersection H A beta t := by
  have htG := subgroup_flip_mem_ambient hzA ht
  have hsG := subgroup_flip_mem_ambient hzA hs
  have hI := pair_inverted_set_eq_products h S hzS hzcenter
    (subgroupRightCosetInclusion_ne_base H A hbeta) htG
  have hprod : (s : G) * t ∈
      pairInvertedSet H (subgroupRightCosetInclusion H A beta) (t : G) := by
    rw [hI]
    exact ⟨(s : G), hsG, rfl⟩
  have hzorder : orderOf (⟨z, hzA⟩ : A) = 2 := by
    simpa only [Subgroup.orderOf_mk] using h.distinguished_order
  exact ⟨hprod.1, pairPointStabilizer_le_pairFlipGroup _ _ _
    (pair_flip_product_mem hzorder ht hs)⟩

theorem subgroup_pair_flip_mem_odd_coset [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) {t s : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta)
    (hs : s ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    ∃ n : subgroupPairOddIntersection H A beta t, t * (n : A) = s := by
  have hzorder : orderOf (⟨z, hzA⟩ : A) = 2 := by
    simpa only [Subgroup.orderOf_mk] using h.distinguished_order
  have htorder := order_two_of_mem_pointClass hzorder ht.1
  have hsorder := order_two_of_mem_pointClass hzorder hs.1
  have hprod := subgroup_pair_flip_product_mem_intersection h hzA S hzS hzcenter hbeta ht hs
  have hts : t * s ∈ subgroupPairOddIntersection H A beta t := by
    have hh := (subgroupPairOddIntersection H A beta t).inv_mem hprod
    simpa only [mul_inv_rev, inv_eq_self_of_orderOf_eq_two htorder,
      inv_eq_self_of_orderOf_eq_two hsorder] using hh
  refine ⟨⟨t * s, hts⟩, ?_⟩
  have htt : t * t = 1 := by
    simpa only [pow_two] using (orderOf_eq_prime_iff.mp htorder).1
  change t * (t * s) = s
  rw [← mul_assoc, htt, one_mul]

theorem subgroup_pair_flip_fiber_eq_odd_class [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) {t : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta =
      conjugacyWithin (subgroupPairOddIntersection H A beta t) t := by
  let KA := pairFlipGroup (H.subgroupOf A) beta t
  let N := subgroupPairOddIntersection H A beta t
  have hNle : N ≤ KA := inf_le_right
  have hN := subgroup_pair_odd_intersection_normal_odd h hzA hbeta ht
  let : (N.subgroupOf KA).Normal := hN.1
  have hNodd : Odd (Nat.card (N.subgroupOf KA)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv]
    exact hN.2
  have hzorder : orderOf (⟨z, hzA⟩ : A) = 2 := by
    simpa only [Subgroup.orderOf_mk] using h.distinguished_order
  let tK : KA := ⟨t, flip_mem_pairFlipGroup _ _ _⟩
  have htI : IsInvolution tK := (orderOf_eq_prime_iff.mp
    (by rw [Subgroup.orderOf_mk]; exact order_two_of_mem_pointClass hzorder ht.1)).symm
  ext s
  constructor
  · intro hs
    let sK : KA := ⟨s, pair_flip_mem_group hzorder ht hs⟩
    have hsI : IsInvolution sK := (orderOf_eq_prime_iff.mp
      (by rw [Subgroup.orderOf_mk]; exact order_two_of_mem_pointClass hzorder hs.1)).symm
    have hprod : sK * tK ∈ N.subgroupOf KA :=
      subgroup_pair_flip_product_mem_intersection h hzA S hzS hzcenter hbeta ht hs
    obtain ⟨n, hn⟩ := involution_mem_odd_normal_class hNodd hsI htI hprod
    refine ⟨⟨((n : KA) : A), n.property⟩, ?_⟩
    exact congrArg (fun k : KA => (k : A)) hn
  · rintro ⟨n, rfl⟩
    exact pair_group_conjugate_flip_mem hzorder hbeta ht ht (hNle n.property)

end CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
