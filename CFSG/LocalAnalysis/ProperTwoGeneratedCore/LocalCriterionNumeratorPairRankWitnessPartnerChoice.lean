module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessNonnesting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem numeratorPairRank_product_partner_join (u v : G) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers (u * v) =
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Subgroup.zpowers_le.mpr
    exact (Subgroup.zpowers u ⊔ Subgroup.zpowers v).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  · apply sup_le le_sup_left
    apply Subgroup.zpowers_le.mpr
    have hmem := (Subgroup.zpowers u ⊔ Subgroup.zpowers (u * v)).mul_mem
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers (u * v)).inv_mem
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers (u * v)))
    simpa only [inv_mul_cancel_left] using hmem

theorem numeratorPairRank_product_partner_common_class
    (H : Subgroup G) (z u v : G) :
    numeratorPairRankPointClass H z u ∩ numeratorPairRankPointClass H z (u * v) =
      numeratorPairRankPointClass H z u ∩ numeratorPairRankPointClass H z v := by
  ext x
  constructor
  · rintro ⟨hxu, hxuv⟩
    have hcommu : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hxu.2
    have hcommuv : Commute x (u * v) :=
      Subgroup.mem_centralizer_singleton_iff.mp hxuv.2
    have hcommv : Commute x v := by
      simpa only [inv_mul_cancel_left] using hcommu.inv_right.mul_right hcommuv
    exact ⟨hxu, ⟨hxuv.1, Subgroup.mem_centralizer_singleton_iff.mpr hcommv.eq⟩⟩
  · rintro ⟨hxu, hxv⟩
    have hcommu : Commute x u := Subgroup.mem_centralizer_singleton_iff.mp hxu.2
    have hcommv : Commute x v := Subgroup.mem_centralizer_singleton_iff.mp hxv.2
    exact ⟨hxu, ⟨hxv.1,
      Subgroup.mem_centralizer_singleton_iff.mpr (hcommu.mul_right hcommv).eq⟩⟩

theorem numeratorPairRank_product_partner_conjugation_on_first_hull
    (z u v x : G) (hx : x ∈ localInvolutionPointHull z u) :
    rightConjugateElem x (u * v) = rightConjugateElem x v := by
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z u hx)
  have hcancel : u⁻¹ * x * u = x := by
    rw [mul_assoc, hxu, inv_mul_cancel_left]
  unfold rightConjugateElem
  calc
    (u * v)⁻¹ * x * (u * v) = v⁻¹ * (u⁻¹ * x * u) * v := by group
    _ = v⁻¹ * x * v := by rw [hcancel]

theorem numeratorPairRank_actor_centralizes_class_iff
    (H : Subgroup G) (z u v : G) :
    v ∈ Subgroup.centralizer (numeratorPairRankPointClass H z u) ↔
      numeratorPairRankPointClass H z u ⊆ numeratorPairRankPointClass H z v := by
  constructor
  · intro hv x hx
    exact ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hv x hx)⟩
  · intro hsub
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hx).2

theorem numeratorPairRank_product_partner_involution
    (u v : G) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huv : Commute u v) (hvu : v ≠ u) :
    orderOf (u * v) = 2 ∧ u * v ≠ u ∧ Commute u (u * v) := by
  have hsq : (u * v) ^ 2 = 1 := by
    rw [huv.mul_pow, (orderOf_eq_prime_iff.mp hu).1,
      (orderOf_eq_prime_iff.mp hv).1, mul_one]
  have hne : u * v ≠ 1 := by
    intro heq
    have h := mul_eq_one_iff_eq_inv.mp heq
    rw [inv_eq_self_of_orderOf_eq_two hv] at h
    exact hvu h.symm
  refine ⟨orderOf_eq_prime_iff.mpr ⟨hsq, hne⟩, ?_, (Commute.refl u).mul_right huv⟩
  intro heq
  have hvone : v = 1 := mul_left_cancel (heq.trans (mul_one u).symm)
  exact (orderOf_eq_prime_iff.mp hv).2 hvone

variable [Finite G]

theorem numeratorPairRank_nonnested_bounded_partner_moves_both
    (H : Subgroup G) (z u v : G)
    (hcard : Nat.card (numeratorPairRankPointClass H z v) ≤
      Nat.card (numeratorPairRankPointClass H z u))
    (hnonnested : ¬ numeratorPairRankPointClass H z v ⊆
      numeratorPairRankPointClass H z u) :
    v ∉ Subgroup.centralizer (numeratorPairRankPointClass H z u) ∧
      u ∉ Subgroup.centralizer (numeratorPairRankPointClass H z v) := by
  constructor
  · intro hv
    have hsub := (numeratorPairRank_actor_centralizes_class_iff H z u v).mp hv
    have heq := numeratorPairRank_class_eq_of_subset_of_card_le hsub hcard
    apply hnonnested
    rw [← heq]
  · intro hu
    exact hnonnested ((numeratorPairRank_actor_centralizes_class_iff H z v u).mp hu)

theorem original_maximum_four_group_select_both_moving_roots
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
    ∃ w : G, (w = v ∨ w = u * v) ∧
      w ∈ pairPointStabilizer H beta ∧ orderOf w = 2 ∧ w ≠ u ∧
      Commute u w ∧ Commute w t ∧
      Subgroup.zpowers u ⊔ Subgroup.zpowers w =
        Subgroup.zpowers u ⊔ Subgroup.zpowers v ∧
      IsElemAbelian 2 (Subgroup.zpowers u ⊔ Subgroup.zpowers w) ∧
      Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers w : Subgroup G) = 4 ∧
      (¬ numeratorPairRankPointClass H z w ⊆ numeratorPairRankPointClass H z u) ∧
      w ∉ Subgroup.centralizer (numeratorPairRankPointClass H z u) ∧
      u ∉ Subgroup.centralizer (numeratorPairRankPointClass H z w) ∧
      numeratorPairRankPointClass H z u ∩ numeratorPairRankPointClass H z w =
        numeratorPairRankPointClass H z u ∩ numeratorPairRankPointClass H z v ∧
      ∀ x ∈ localInvolutionPointHull z u,
        rightConjugateElem x w = rightConjugateElem x v := by
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
    have hWC : W ≤ Subgroup.centralizer ({t} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hvt.eq))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWC hw)
  have hno := original_pair_four_group_has_nonnested_partner hnonab h S hzS hzcenter
    hbeta ht hgen W hcard u v (numeratorPairRank_pair_join_eq_closure u v)
    hWB hzW htW
  rcases hno with hno | hno
  · obtain ⟨hvmove, humove⟩ := numeratorPairRank_nonnested_bounded_partner_moves_both
      H z u v (hmax v hvB hv hvt) hno
    exact ⟨v, Or.inl rfl, hvB, hv, hvu, huv, hvt, rfl, helem, hcard,
      hno, hvmove, humove, rfl, fun _ _ => rfl⟩
  · obtain ⟨huvorder, huvne, huuv⟩ :=
      numeratorPairRank_product_partner_involution u v hu hv huv hvu
    have huvB := (pairPointStabilizer H beta).mul_mem huB hvB
    have huvT := hut.mul_left hvt
    have hjoin := numeratorPairRank_product_partner_join u v
    obtain ⟨huvmove, humove⟩ := numeratorPairRank_nonnested_bounded_partner_moves_both
      H z u (u * v) (hmax (u * v) huvB huvorder huvT) hno
    refine ⟨u * v, Or.inr rfl, huvB, huvorder, huvne, huuv, huvT, hjoin,
      hjoin.symm ▸ helem, hjoin.symm ▸ hcard, hno, huvmove, humove,
      numeratorPairRank_product_partner_common_class H z u v, ?_⟩
    intro x hx
    exact numeratorPairRank_product_partner_conjugation_on_first_hull z u v x hx

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
