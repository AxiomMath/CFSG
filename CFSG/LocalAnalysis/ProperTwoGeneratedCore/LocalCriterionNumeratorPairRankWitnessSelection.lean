module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessFourGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankMaximalKernel

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

theorem original_pair_flip_centralizer_factorization
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    ∀ b ∈ pairPointStabilizer H beta,
      ∃ c ∈ pairPointStabilizer H beta ⊓ Subgroup.centralizer ({t} : Set G),
        ∃ x ∈ pairOddCore H beta, b = c * x := by
  intro b hb
  obtain ⟨c, hc, x, hx, hcx⟩ :=
    (pair_flip_zStar_factorization h S hzS hzcenter hbeta ht).2 b
      (pairPointStabilizer_le_pairFlipGroup H beta t hb)
  have hcB : c ∈ pairPointStabilizer H beta := by
    have hxB := (pairOddCore_le H beta t).1 hx
    have hmem := (pairPointStabilizer H beta).mul_mem hb
      ((pairPointStabilizer H beta).inv_mem hxB)
    simpa only [hcx, mul_inv_cancel_right] using hmem
  exact ⟨c, ⟨hcB, hc.2⟩, x, hx, hcx⟩

omit [Finite G] in
theorem subgroup_index_eq_relative_of_factorization
    (C J : Subgroup G)
    (hfactor : ∀ g : G, ∃ c ∈ C, ∃ j ∈ J, g = c * j) :
    C.index = C.relIndex J := by
  let f := Subgroup.quotientSubgroupOfEmbeddingOfLE C (show J ≤ ⊤ from le_top)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    obtain ⟨c, hc, j, hj, hgj⟩ := hfactor (g : G)⁻¹
    refine ⟨QuotientGroup.mk (⟨j⁻¹, J.inv_mem hj⟩ : J), ?_⟩
    apply QuotientGroup.eq.mpr
    change j⁻¹⁻¹ * (g : G) ∈ C
    rw [inv_inv]
    have hgeq : (g : G) = j⁻¹ * c⁻¹ := by
      have hinv := congrArg Inv.inv hgj
      simpa only [inv_inv, mul_inv_rev] using hinv
    rw [hgeq, ← mul_assoc, mul_inv_cancel, one_mul]
    exact C.inv_mem hc
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hsurj⟩)
  change C.relIndex J = C.relIndex ⊤ at hcard
  simpa only [Subgroup.relIndex_top_right] using hcard.symm

theorem original_pair_flip_centralizer_index_odd
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta) :
    Odd ((Subgroup.centralizer ({t} : Set G)).subgroupOf
      (pairPointStabilizer H beta)).index := by
  let B := pairPointStabilizer H beta
  let C := (Subgroup.centralizer ({t} : Set G)).subgroupOf B
  let J := (pairOddCore H beta).subgroupOf B
  have hfactor : ∀ b : B, ∃ c ∈ C, ∃ j ∈ J, b = c * j := by
    intro b
    obtain ⟨c, hc, j, hj, hbj⟩ :=
      original_pair_flip_centralizer_factorization h S hzS hzcenter hbeta ht b b.property
    exact ⟨⟨c, hc.1⟩, hc.2, ⟨j, (pairOddCore_le H beta t).1 hj⟩, hj,
      Subtype.ext hbj⟩
  have hindex : C.index = C.relIndex J :=
    subgroup_index_eq_relative_of_factorization C J hfactor
  have hJodd : Odd (Nat.card J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pairOddCore_le H beta t).1).toEquiv]
    exact pairOddCore_odd H beta
  change Odd C.index
  rw [hindex]
  exact hJodd.of_dvd_nat (C.relIndex_dvd_card J)

theorem odd_index_involution_has_native_four_group
    (C : Subgroup G) (hindex : Odd C.index) (hrank : 2 ≤ twoRank G)
    (a : C) (ha : orderOf a = 2) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ C ∧ (a : G) ∈ T ∧
      ∃ b : G, b ∈ (T : Subgroup G) ∧ orderOf b = 2 ∧ b ≠ (a : G) ∧
        Commute (a : G) b ∧
        IsElemAbelian 2 (Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers b) ∧
        Nat.card (Subgroup.zpowers (a : G) ⊔ Subgroup.zpowers b : Subgroup G) = 4 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyclic : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)
  obtain ⟨P, hP⟩ := hcyclic.exists_le_sylow
  have haP : a ∈ (P : Subgroup C) := hP (Subgroup.mem_zpowers a)
  let T := sylowTwoOfOddIndex C hindex P
  have hT : (T : Subgroup G) = (P : Subgroup C).map C.subtype :=
    sylowTwoOfOddIndex_subgroup C hindex P
  have hTC : (T : Subgroup G) ≤ C := by
    rw [hT]
    exact Subgroup.map_subtype_le _
  have haT : (a : G) ∈ (T : Subgroup G) := by
    rw [hT]
    exact Subgroup.mem_map.mpr ⟨a, haP, rfl⟩
  let aT : (T : Subgroup G) := ⟨a, haT⟩
  have haTorder : orderOf aT = 2 :=
    (Subgroup.orderOf_coe aT).symm.trans ((Subgroup.orderOf_coe a).trans ha)
  have hrankT : 2 ≤ twoRank (T : Subgroup G) := by
    rw [CFSG.ComponentClassification.TwoRankSylow.invariant T]
    exact hrank
  obtain ⟨b, hb, hba, hab, _hV, _hcard⟩ :=
    two_group_rank_two_involution_in_four_group T.isPGroup' hrankT aT haTorder
  have hbG : orderOf (b : G) = 2 := (Subgroup.orderOf_coe b).trans hb
  have hbaG : (b : G) ≠ (a : G) := fun heq => hba (Subtype.ext heq)
  have habG : Commute (a : G) (b : G) := congrArg Subtype.val hab.eq
  obtain ⟨helem, hcard, _⟩ := commuting_distinct_involutions_four_group
    ((Subgroup.orderOf_coe a).trans ha) hbG habG hbaG
  exact ⟨T, hTC, haT, b, b.property, hbG, hbaG, habG, helem, hcard⟩

theorem original_pair_maximum_involution_four_group_and_common_root
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    Odd ((Subgroup.centralizer ({t} : Set G)).subgroupOf
      (pairPointStabilizer H beta)).index ∧
    ∃ u v z₀ : G,
      u ∈ pairPointStabilizer H beta ∧ orderOf u = 2 ∧ Commute u t ∧
      v ∈ pairPointStabilizer H beta ∧ orderOf v = 2 ∧ v ≠ u ∧
      Commute u v ∧ Commute v t ∧
      (∀ w : G, w ∈ pairPointStabilizer H beta → orderOf w = 2 → Commute w t →
        Nat.card (numeratorPairRankPointClass H z w) ≤
          Nat.card (numeratorPairRankPointClass H z u)) ∧
      IsElemAbelian 2 (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) = 4 ∧
      z₀ ∈ conjugacyWithin H z ∧
      z₀ ∈ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) ∧
      t ∈ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  classical
  let B := pairPointStabilizer H beta
  let C := (Subgroup.centralizer ({t} : Set G)).subgroupOf B
  have hindex : Odd C.index :=
    original_pair_flip_centralizer_index_odd h S hzS hzcenter hbeta ht
  have hCtwo : 2 ≤ twoRank C := by
    let P : Sylow 2 C := Classical.choice (inferInstance : Nonempty (Sylow 2 C))
    let T := sylowTwoOfOddIndex C hindex P
    have hTC : (T : Subgroup B) ≤ C := by
      rw [sylowTwoOfOddIndex_subgroup]
      exact Subgroup.map_subtype_le _
    have hle := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_injective
      (Subgroup.inclusion hTC) (Subgroup.inclusion_injective hTC)
    rw [CFSG.ComponentClassification.TwoRankSylow.invariant T] at hle
    exact hrank.trans hle
  have hCfour : ∃ V : Subgroup C, IsElemAbelian 2 V ∧ Nat.card V = 4 := by
    by_contra hno
    push Not at hno
    have hbound := twoRank_le_one_of_no_four_group hno
    omega
  obtain ⟨V, hV, hVcard⟩ := hCfour
  obtain ⟨a, _haV, ha, _haone⟩ := elementary_four_exists_involution_ne V hV hVcard 1
  let Actors := {a : C // orderOf a = 2}
  have : Nonempty Actors := ⟨⟨a, ha⟩⟩
  obtain ⟨a₀, ha₀max⟩ := Finite.exists_max
    (fun a : Actors => Nat.card (numeratorPairRankPointClass H z ((a : C) : B)))
  let uB : B := (a₀ : C)
  have huC : uB ∈ C := (a₀ : C).property
  have huorder : orderOf uB = 2 :=
    (Subgroup.orderOf_coe (a₀ : C)).trans a₀.property
  obtain ⟨T, hTC, _huT, vB, hvT, hvorder, hvne, huv, _hW, _hWcard⟩ :=
    odd_index_involution_has_native_four_group C hindex hrank (a₀ : C) a₀.property
  let W := Subgroup.zpowers (uB : G) ⊔ Subgroup.zpowers (vB : G)
  have hu : orderOf (uB : G) = 2 := (Subgroup.orderOf_coe uB).trans huorder
  have hv : orderOf (vB : G) = 2 := (Subgroup.orderOf_coe vB).trans hvorder
  have hvneG : (vB : G) ≠ (uB : G) := fun heq => hvne (Subtype.ext heq)
  have huvG : Commute (uB : G) (vB : G) := congrArg Subtype.val huv.eq
  have hut : Commute (uB : G) t := Subgroup.mem_centralizer_singleton_iff.mp huC
  have hvt : Commute (vB : G) t := Subgroup.mem_centralizer_singleton_iff.mp (hTC hvT)
  obtain ⟨helem, hcard, _⟩ := commuting_distinct_involutions_four_group hu hv huvG hvneG
  have hWB : W ≤ B := sup_le (Subgroup.zpowers_le.mpr uB.property)
    (Subgroup.zpowers_le.mpr vB.property)
  have hWH : W ≤ H := hWB.trans (pairPointStabilizer_le_point H beta)
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by
    exact hcard.trans (by norm_num))
  obtain ⟨z₀, hz₀, hz₀W⟩ := original_two_subgroup_has_common_point_root
    h S hzS hzcenter W hWH hWp
  have htW : t ∈ Subgroup.centralizer (W : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro w hw
    have hWC : W ≤ Subgroup.centralizer ({t} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvt.eq))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
  refine ⟨hindex, uB, vB, z₀, uB.property, hu, hut, vB.property, hv, hvneG,
    huvG, hvt, ?_, helem, hcard, hz₀, hz₀W, htW⟩
  intro w hwB hw hwt
  let wB : B := ⟨w, hwB⟩
  let wC : C := ⟨wB, Subgroup.mem_centralizer_singleton_iff.mpr hwt.eq⟩
  have hwC : orderOf wC = 2 := (Subgroup.orderOf_coe wC).symm.trans
    ((Subgroup.orderOf_coe wB).symm.trans hw)
  exact ha₀max (⟨wC, hwC⟩ : Actors)

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
