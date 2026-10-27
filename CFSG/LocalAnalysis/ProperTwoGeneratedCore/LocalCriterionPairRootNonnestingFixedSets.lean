module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFixedRootFull

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting

open CFSG
open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

universe u

variable {G : Type u} [Group G]

@[expose] def rootFixedSet (H : Subgroup G) (z w : G) : Set G :=
  conjugacyWithin H z ∩ (Subgroup.centralizer ({w} : Set G) : Set G)

@[expose] def commonRootFixedSet (H : Subgroup G) (z : G) (W : Subgroup G) : Set G :=
  conjugacyWithin H z ∩ (Subgroup.centralizer (W : Set G) : Set G)

theorem centralizer_generated_pair (u v : G) :
    Subgroup.centralizer (Subgroup.closure ({u, v} : Set G) : Set G) =
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({v} : Set G) := by
  rw [Subgroup.centralizer_closure]
  ext x
  constructor
  · intro hx
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hx' u (by simp)).symm,
      Subgroup.mem_centralizer_singleton_iff.mpr (hx' v (by simp)).symm⟩
  · rintro ⟨hxu, hxv⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hxu).symm
    · have ha' : a = v := ha
      subst a
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxv).symm

theorem commonRootFixedSet_eq_inter (H : Subgroup G) (z u v : G)
    (W : Subgroup G) (hW : W = Subgroup.closure ({u, v} : Set G)) :
    commonRootFixedSet H z W = rootFixedSet H z u ∩ rootFixedSet H z v := by
  rw [commonRootFixedSet, hW, centralizer_generated_pair]
  ext x
  change (x ∈ conjugacyWithin H z ∧
    x ∈ Subgroup.centralizer ({u} : Set G) ∧ x ∈ Subgroup.centralizer ({v} : Set G)) ↔
    (x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer ({u} : Set G)) ∧
      (x ∈ conjugacyWithin H z ∧ x ∈ Subgroup.centralizer ({v} : Set G))
  tauto

theorem nested_second_eq_common (H : Subgroup G) (z u v : G)
    (W : Subgroup G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hvu : rootFixedSet H z v ⊆ rootFixedSet H z u) :
    rootFixedSet H z v = commonRootFixedSet H z W := by
  rw [commonRootFixedSet_eq_inter H z u v W hW]
  exact (Set.inter_eq_right.mpr hvu).symm

theorem nested_product_eq_common (H : Subgroup G) (z u v : G)
    (W : Subgroup G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (huvu : rootFixedSet H z (u * v) ⊆ rootFixedSet H z u) :
    rootFixedSet H z (u * v) = commonRootFixedSet H z W := by
  rw [commonRootFixedSet_eq_inter H z u v W hW]
  apply Set.Subset.antisymm
  · intro x hx
    have hxu := huvu hx
    have hxU : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hxu.2
    have hxUV : Commute x (u * v) := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hxV : Commute x v := by
      simpa only [inv_mul_cancel_left] using hxU.inv_right.mul_right hxUV
    exact ⟨hxu, hx.1, Subgroup.mem_centralizer_singleton_iff.mpr hxV.eq⟩
  · rintro x ⟨hxu, hxv⟩
    have hxU : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hxu.2
    have hxV : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hxv.2
    exact ⟨hxu.1, Subgroup.mem_centralizer_singleton_iff.mpr (hxU.mul_right hxV).eq⟩

theorem elementary_four_group_generators [Finite G]
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G)) :
    u ∈ W ∧ v ∈ W ∧ orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v := by
  have huW : u ∈ W := by
    rw [hW]
    exact Subgroup.subset_closure (by simp)
  have hvW : v ∈ W := by
    rw [hW]
    exact Subgroup.subset_closure (by simp)
  have hnotcyclic (a : G) (ha : a ∈ W) : ¬ W ≤ Subgroup.zpowers a := by
    intro hle
    have hcardle := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    have horderle : orderOf a ≤ 2 := Nat.le_of_dvd (by decide)
      (orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian a ha))
    rw [hcardW, Nat.card_zpowers] at hcardle
    omega
  have huone : u ≠ 1 := by
    intro hu
    apply hnotcyclic v hvW
    rw [hW]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    change a ∈ Subgroup.zpowers v
    rcases Set.mem_insert_iff.mp ha with hau | ha
    · rw [hau, hu]
      exact (Subgroup.zpowers v).one_mem
    · have ha' : a = v := ha
      rw [ha']
      exact Subgroup.mem_zpowers v
  have hvone : v ≠ 1 := by
    intro hv
    apply hnotcyclic u huW
    rw [hW]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    change a ∈ Subgroup.zpowers u
    rcases Set.mem_insert_iff.mp ha with hau | ha
    · rw [hau]
      exact Subgroup.mem_zpowers u
    · have ha' : a = v := ha
      rw [ha', hv]
      exact (Subgroup.zpowers u).one_mem
  have huv : u ≠ v := by
    intro huv
    apply hnotcyclic u huW
    rw [hW]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    change a ∈ Subgroup.zpowers u
    rcases Set.mem_insert_iff.mp ha with hau | ha
    · rw [hau]
      exact Subgroup.mem_zpowers u
    · have ha' : a = v := ha
      rw [ha', ← huv]
      exact Subgroup.mem_zpowers u
  exact ⟨huW, hvW,
    orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian u huW, huone⟩,
    orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian v hvW, hvone⟩, huv⟩

theorem common_root_card_pos [Finite G] (H : Subgroup G) (z : G) (W : Subgroup G)
    (hzW : z ∈ Subgroup.centralizer (W : Set G)) :
    0 < Nat.card (commonRootFixedSet H z W) := by
  have hzclass : z ∈ conjugacyWithin H z := by
    refine ⟨1, ?_⟩
    simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]
  let : Nonempty (commonRootFixedSet H z W) := ⟨⟨z, hzclass, hzW⟩⟩
  exact Nat.card_pos

theorem original_nested_root_sets_eq_entire_class [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hcardW : Nat.card W = 4)
    (u v : G) (hW : W = Subgroup.closure ({u, v} : Set G))
    (hWB : W ≤ pairPointStabilizer H beta)
    (hzW : z ∈ Subgroup.centralizer (W : Set G))
    (htW : t ∈ Subgroup.centralizer (W : Set G))
    (hvu : rootFixedSet H z v ⊆ rootFixedSet H z u)
    (huvu : rootFixedSet H z (u * v) ⊆ rootFixedSet H z u) :
    rootFixedSet H z u = conjugacyWithin H z := by
  classical
  let : Fintype W := Fintype.ofFinite W
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hcardW
  obtain ⟨huW, hvW, hu, hv, huv⟩ := elementary_four_group_generators W hcardW u v hW
  let a : W := ⟨u, huW⟩
  let b : W := ⟨v, hvW⟩
  have ha : a ≠ 1 := fun heq => (orderOf_eq_prime_iff.mp hu).2 (congrArg Subtype.val heq)
  have hb : b ≠ 1 := fun heq => (orderOf_eq_prime_iff.mp hv).2 (congrArg Subtype.val heq)
  have hab : a ≠ b := fun heq => huv (congrArg Subtype.val heq)
  have hidentity := original_fixed_root_four_group_cardinality_identity
    h S hzS hzcenter hbeta ht W hcardW hWB hzW htW
  dsimp only at hidentity
  rw [kleinFour_prod_nonidentity _ a b ha hb hab] at hidentity
  simp only [centralizer_zpowers_eq_singleton, a, b, Subgroup.coe_mul] at hidentity
  change Nat.card (conjugacyWithin H z) * (Nat.card (commonRootFixedSet H z W)) ^ 2 =
    Nat.card (rootFixedSet H z u) * Nat.card (rootFixedSet H z v) *
      Nat.card (rootFixedSet H z (u * v)) at hidentity
  rw [nested_second_eq_common H z u v W hW hvu,
    nested_product_eq_common H z u v W hW huvu] at hidentity
  have heq : Nat.card (rootFixedSet H z u) = Nat.card (conjugacyWithin H z) := by
    apply (Nat.eq_of_mul_eq_mul_right
      (pow_pos (common_root_card_pos H z W hzW) 2) ?_).symm
    simpa only [pow_two, mul_assoc] using hidentity
  apply Set.eq_of_subset_of_ncard_le (fun _ hx => hx.1)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact heq.ge

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairRootNonnesting
