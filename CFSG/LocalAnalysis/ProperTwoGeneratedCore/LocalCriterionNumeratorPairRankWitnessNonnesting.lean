module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairRootNonnestingFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem numeratorPairRank_pair_join_eq_closure (u v : G) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers v = Subgroup.closure ({u, v} : Set G) := by
  have hpair : ({u, v} : Set G) = {u} ∪ {v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  rw [hpair, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure]

theorem numeratorPairRankPointClass_eq_rootFixedSet
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (w : G) :
    numeratorPairRankPointClass H z w = rootFixedSet H z w := by
  rw [numeratorPairRankPointClass, rootFixedSet,
    original_point_class_intersection_eq_conjugacyWithin h]

variable [Finite G]

omit [Group G] in
theorem numeratorPairRank_class_eq_of_subset_of_card_le
    {A B : Set G} (hAB : A ⊆ B) (hcard : Nat.card B ≤ Nat.card A) : A = B := by
  apply Set.eq_of_subset_of_ncard_le hAB
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact hcard

theorem original_maximum_pair_partner_moves_root
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤)
    (u v : G) (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2)
    (hvB : v ∈ pairPointStabilizer H beta) (hv : orderOf v = 2)
    (hvu : v ≠ u) (huv : Commute u v) (hut : Commute u t) (hvt : Commute v t)
    (hzW : z ∈ Subgroup.centralizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G))
    (hmax : ∀ w : G, w ∈ pairPointStabilizer H beta → orderOf w = 2 → Commute w t →
      Nat.card (numeratorPairRankPointClass H z w) ≤
        Nat.card (numeratorPairRankPointClass H z u)) :
    v ∉ Subgroup.centralizer (numeratorPairRankPointClass H z u) := by
  intro hvcentral
  let W := Subgroup.zpowers u ⊔ Subgroup.zpowers v
  obtain ⟨helem, hcard, _⟩ := commuting_distinct_involutions_four_group hu hv huv hvu
  let : CFSG.IsElementaryAbelian 2 W :=
    { toIsMulCommutative := helem.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w => by
        apply Subtype.ext
        exact helem.2 w w.property) }
  have hWB : W ≤ pairPointStabilizer H beta :=
    sup_le (Subgroup.zpowers_le.mpr huB) (Subgroup.zpowers_le.mpr hvB)
  have htW : t ∈ Subgroup.centralizer (W : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro w hw
    have hWcentral : W ≤ Subgroup.centralizer ({t} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvt.eq))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWcentral hw)
  have huvorder : orderOf (u * v) = 2 := by
    have huvW : u * v ∈ W := W.mul_mem
      ((show Subgroup.zpowers u ≤ W from le_sup_left) (Subgroup.mem_zpowers u))
      ((show Subgroup.zpowers v ≤ W from le_sup_right) (Subgroup.mem_zpowers v))
    apply orderOf_eq_prime_iff.mpr
    refine ⟨helem.2 _ huvW, ?_⟩
    intro heq
    have h := mul_eq_one_iff_eq_inv.mp heq
    rw [inv_eq_self_of_orderOf_eq_two hv] at h
    exact hvu h.symm
  have huvB : u * v ∈ pairPointStabilizer H beta :=
    (pairPointStabilizer H beta).mul_mem huB hvB
  have hrootv : numeratorPairRankPointClass H z u ⊆ numeratorPairRankPointClass H z v := by
    intro x hx
    exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hvcentral x hx)⟩
  have hrootuv : numeratorPairRankPointClass H z u ⊆
      numeratorPairRankPointClass H z (u * v) := by
    intro x hx
    have hxu : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp (hrootv hx).2
    exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (hxu.mul_right hxv).eq⟩
  have heqv := numeratorPairRank_class_eq_of_subset_of_card_le hrootv (hmax v hvB hv hvt)
  have hequv := numeratorPairRank_class_eq_of_subset_of_card_le hrootuv
    (hmax (u * v) huvB huvorder (hut.mul_left hvt))
  have hno := original_pair_generated_four_group_root_centralizer_nonnesting
    hnonab h S hzS hzcenter hbeta ht hgen W hcard u v
    (numeratorPairRank_pair_join_eq_closure u v) hWB hzW htW
  simp_rw [← numeratorPairRankPointClass_eq_rootFixedSet h] at hno
  rcases hno with hno | hno
  · exact hno (heqv ▸ Set.Subset.refl _)
  · exact hno (hequv ▸ Set.Subset.refl _)

theorem original_pair_four_group_has_nonnested_partner
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hgen : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔ pairOddCore H beta = ⊤)
    (W : Subgroup G) [CFSG.IsElementaryAbelian 2 W] (hcard : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G)) :
    ¬ numeratorPairRankPointClass H z v ⊆ numeratorPairRankPointClass H z u ∨
      ¬ numeratorPairRankPointClass H z (u * v) ⊆ numeratorPairRankPointClass H z u := by
  simpa only [numeratorPairRankPointClass_eq_rootFixedSet h] using
    original_pair_generated_four_group_root_centralizer_nonnesting
      hnonab h S hzS hzcenter hbeta ht hgen W hcard u v hW hWB hzW htW

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
