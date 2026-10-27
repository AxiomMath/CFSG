module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.HighRankPairWitnessPrime
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankWitnessMovingRoots

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionFixedRoot
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
open CFSG.BenderSuzuki.PFAppendixIII

universe u

variable {G : Type u} [Group G]

theorem distinguishedRoots_eq_pointRoots [Finite G] {H : Subgroup G} {z z₀ : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hpoint : conjugacyWithin H z₀ = conjugacyWithin H z) (w : G) :
    distinguishedRoots H z w = pointRoots H z₀ w := by
  unfold distinguishedRoots pointRoots
  rw [hpoint, ← original_point_class_intersection_eq_conjugacyWithin h.local_datum]

theorem pointRoots_inter_centralizer (H : Subgroup G) (z₀ w y : G) :
    pointRoots H z₀ w ∩ (Subgroup.centralizer ({y} : Set G) : Set G) =
      pointRoots H z₀ w ∩ pointRoots H z₀ y := by
  ext x
  simp only [pointRoots, Set.mem_inter_iff]
  tauto

theorem pointRoots_mul_inter (H : Subgroup G) (z₀ u v : G) :
    pointRoots H z₀ (u * v) ∩ pointRoots H z₀ u = pointRoots H z₀ u ∩ pointRoots H z₀ v := by
  ext x
  simp only [pointRoots, Set.mem_inter_iff, SetLike.mem_coe,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨⟨hx, huv⟩, -, hu⟩
    refine ⟨⟨hx, hu⟩, hx, ?_⟩
    have h1 : Commute x (u * v) := huv
    have h2 : Commute x u := hu
    have h3 := h2.inv_right.mul_right h1
    rwa [inv_mul_cancel_left] at h3
  · rintro ⟨⟨hx, hu⟩, -, hv⟩
    have h1 : Commute x u := hu
    have h2 : Commute x v := hv
    exact ⟨⟨hx, (h1.mul_right h2).eq⟩, hx, hu⟩

theorem not_commute_of_rightConjugateElem_ne {x v : G} (h : rightConjugateElem x v ≠ x) :
    ¬ Commute v x := by
  intro hc
  apply h
  rw [rightConjugateElem, mul_assoc, ← hc.eq, inv_mul_cancel_left]


variable [Finite G]

theorem pow_two_sub_one_inj {a b : ℕ} (h : 2 ^ a - 1 = 2 ^ b - 1) : a = b := by
  have ha : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  exact Nat.pow_right_injective (le_refl 2) (show 2 ^ a = 2 ^ b by omega)

theorem high_rank_pair_square_field_selection {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hgen : PairGenerationTheorem G)
    (hNC : NoncentralPairActionTheorem G)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : 2 ≤ twoRank (pairPointStabilizer H beta)) :
    ∃ z₀ u v : G, ∃ a : ℕ, 1 ≤ a ∧ z₀ ∈ conjugacyWithin H z ∧
      MinimalInvolutionPointLocalFailure H z₀ ∧ conjugacyWithin H z₀ = conjugacyWithin H z ∧
      t ∈ rightPairFlipFiber H z₀ beta ∧
      u ∈ pairPointStabilizer H beta ∧ v ∈ pairPointStabilizer H beta ∧
      orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ Commute u v ∧
      Commute u z₀ ∧ Commute v z₀ ∧ Commute u t ∧ Commute v t ∧
      FieldInvolutionOn (localInvolutionPointHull z u) v a ∧
      FieldInvolutionOn (localInvolutionPointHull z v) u a ∧
      Nat.card (pointRoots H z₀ u) = 2 ^ (2 * a) - 1 ∧
      Nat.card (pointRoots H z₀ v) = 2 ^ (2 * a) - 1 ∧
      Nat.card (pointRoots H z₀ u ∩ pointRoots H z₀ v : Set G) = 2 ^ a - 1 ∧
      (pointRoots H z₀ (u * v) ⊆ pointRoots H z₀ u ∨
        Nat.card (pointRoots H z₀ (u * v)) = 2 ^ (2 * a) - 1 ∧
          FieldInvolutionOn (localInvolutionPointHull z (u * v)) u a) := by
  have hfull : FullPointPairGeneration H z :=
    (fullPointPairGeneration_iff_base h.local_datum).mpr (hgen H z h)
  obtain ⟨u, v, z₀, huB, hu, hut, hvB, hv, hvu, huv, hvt, huz₀, hvz₀, -, -, -, hz₀, -, -,
    h₀, hpoint, -, hhulls, hflips, -, -, -, -, hxu, hxv⟩ :=
    original_high_rank_selected_both_moving_roots h hfull hbeta ht hrank
  have ht₀ : t ∈ rightPairFlipFiber H z₀ beta := by rw [hflips beta]; exact ht
  have hNC₀ := hNC H z₀ h₀ beta hbeta t ht₀
  have hroots := distinguishedRoots_eq_pointRoots h hpoint
  have hmove : ∀ w y : G, (∃ x ∈ numeratorPairRankPointClass H z w, rightConjugateElem x y ≠ x) →
      ∃ x ∈ pointRoots H z₀ w, ¬ Commute y x := by
    rintro w y ⟨x, hx, hxy⟩
    refine ⟨x, ?_, not_commute_of_rightConjugateElem_ne hxy⟩
    rw [← hroots]
    exact hx
  obtain ⟨a, ha, hFu, -, hcardu, hcardW⟩ :=
    hNC₀ u v huB hu huz₀ hut hvB hv huv (hmove u v hxu)
  obtain ⟨a₁, -, hFv, -, hcardv, hcardW₁⟩ :=
    hNC₀ v u hvB hv hvz₀ hvt huB hu huv.symm (hmove v u hxv)
  rw [pointRoots_inter_centralizer] at hcardW hcardW₁
  rw [Set.inter_comm, hcardW] at hcardW₁
  have ha₁ : a₁ = a := (pow_two_sub_one_inj hcardW₁).symm
  subst ha₁
  rw [hhulls] at hFu hFv
  refine ⟨z₀, u, v, a₁, ha, hz₀, h₀, hpoint, ht₀, huB, hvB, hu, hv, hvu.symm, huv, huz₀, hvz₀,
    hut, hvt, hFu, hFv, hcardu, hcardv, hcardW, ?_⟩
  by_cases hsub : pointRoots H z₀ (u * v) ⊆ pointRoots H z₀ u
  · exact Or.inl hsub
  right
  obtain ⟨y, hyuv, hyu⟩ := Set.not_subset.mp hsub
  have hnc : ¬ Commute u y := fun hc =>
    hyu ⟨hyuv.1, Subgroup.mem_centralizer_singleton_iff.mpr hc.eq.symm⟩
  obtain ⟨huvord, -, hcomm⟩ := numeratorPairRank_product_partner_involution u v hu hv huv hvu
  obtain ⟨a₂, -, hFuv, -, hcarduv, hcardW₂⟩ :=
    hNC₀ (u * v) u ((pairPointStabilizer H beta).mul_mem huB hvB) huvord
      (huz₀.mul_left hvz₀) (hut.mul_left hvt) huB hu hcomm.symm ⟨y, hyuv, hnc⟩
  rw [pointRoots_inter_centralizer, pointRoots_mul_inter, hcardW] at hcardW₂
  have ha₂ : a₂ = a₁ := (pow_two_sub_one_inj hcardW₂).symm
  subst ha₂
  rw [hhulls] at hFuv
  exact ⟨hcarduv, hFuv⟩


theorem high_rank_pair_class_identity {H : Subgroup G} {z₀ : G}
    (h₀ : MinimalInvolutionPointLocalFailure H z₀)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z₀ beta)
    {u v : G} (huB : u ∈ pairPointStabilizer H beta) (hvB : v ∈ pairPointStabilizer H beta)
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : u ≠ v) (hcuv : Commute u v)
    (huz : Commute u z₀) (hvz : Commute v z₀) (hut : Commute u t) (hvt : Commute v t) :
    Nat.card (conjugacyWithin H z₀) *
        Nat.card (pointRoots H z₀ u ∩ pointRoots H z₀ v : Set G) ^ 2 =
      Nat.card (pointRoots H z₀ u) * Nat.card (pointRoots H z₀ v) *
        Nat.card (pointRoots H z₀ (u * v)) := by
  classical
  obtain ⟨S, hzS, hzcenter⟩ := h₀.central_sylow
  set W := Subgroup.zpowers u ⊔ Subgroup.zpowers v with hWdef
  obtain ⟨helem, hWcard, -⟩ := CFSG.ProperTwoGeneratedCore.commuting_distinct_involutions_four_group
    hu hv hcuv huv.symm
  let : IsElementaryAbelian 2 W :=
    { toIsMulCommutative := helem.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w => by
        apply Subtype.ext
        exact helem.2 w w.property) }
  let : IsKleinFour W := isKleinFour_of_elementary_card_four hWcard
  have hWB : W ≤ pairPointStabilizer H beta :=
    sup_le (Subgroup.zpowers_le.mpr huB) (Subgroup.zpowers_le.mpr hvB)
  have hz₀W : z₀ ∈ Subgroup.centralizer (W : Set G) := by
    rw [hWdef, centralizer_pair_join]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr huz.eq.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr hvz.eq.symm⟩
  have htW : t ∈ Subgroup.centralizer (W : Set G) := by
    rw [hWdef, centralizer_pair_join]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr hut.eq.symm,
      Subgroup.mem_centralizer_singleton_iff.mpr hvt.eq.symm⟩
  have hid := (original_fixed_root_cardinality_identity_full h₀.local_datum S hzS hzcenter hbeta ht
    W hWcard hWB hz₀W htW).2
  dsimp only at hid
  let : Fintype W := Fintype.ofFinite W
  let a : W := ⟨u, Subgroup.mem_sup_left (Subgroup.mem_zpowers u)⟩
  let b : W := ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v)⟩
  have ha : a ≠ 1 := fun h1 => by
    have : u = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hu
    omega
  have hb : b ≠ 1 := fun h1 => by
    have : v = 1 := congrArg Subtype.val h1
    rw [this, orderOf_one] at hv
    omega
  have hab : a ≠ b := fun h1 => huv (congrArg Subtype.val h1)
  rw [kleinFour_prod_nonidentity _ a b ha hb hab] at hid
  have hroot : ∀ w : G, Nat.card {x : G // x ∈ conjugacyWithin H z₀ ∧
      x ∈ Subgroup.centralizer (Subgroup.zpowers w : Set G)} = Nat.card (pointRoots H z₀ w) := by
    intro w
    rw [centralizer_zpowers_eq_singleton]
    rfl
  have hcommon : Nat.card {x : G // x ∈ conjugacyWithin H z₀ ∧
      x ∈ Subgroup.centralizer (W : Set G)} =
      Nat.card (pointRoots H z₀ u ∩ pointRoots H z₀ v : Set G) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun x => ?_
    rw [hWdef, centralizer_pair_join]
    simp only [pointRoots, Set.mem_inter_iff, Subgroup.mem_inf, SetLike.mem_coe]
    tauto
  rw [hcommon, hroot, hroot, hroot] at hid
  exact hid


theorem class_size_eq_square {m a : ℕ} (ha : 1 ≤ a)
    (h : m * (2 ^ a - 1) ^ 2 = (2 ^ (2 * a) - 1) * (2 ^ (2 * a) - 1) * (2 ^ a - 1)) :
    m = (2 ^ a - 1) * (2 ^ a + 1) ^ 2 := by
  rw [two_pow_double_sub_one] at h
  have hQ : 0 < 2 ^ a - 1 := Nat.pos_of_ne_zero (two_pow_sub_one_ne_zero ha)
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hQ 2)
  rw [h]
  ring

theorem class_size_eq_cube {m a : ℕ} (ha : 1 ≤ a)
    (h : m * (2 ^ a - 1) ^ 2 = (2 ^ (2 * a) - 1) * (2 ^ (2 * a) - 1) * (2 ^ (2 * a) - 1)) :
    m = (2 ^ a - 1) * (2 ^ a + 1) ^ 3 := by
  rw [two_pow_double_sub_one] at h
  have hQ : 0 < 2 ^ a - 1 := Nat.pos_of_ne_zero (two_pow_sub_one_ne_zero ha)
  apply Nat.eq_of_mul_eq_mul_right (pow_pos hQ 2)
  rw [h]
  ring

end CFSG.ProperTwoGeneratedCore.HighRankPair
