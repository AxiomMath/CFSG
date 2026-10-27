module

public import CFSG.LieType.Ree.LargeReeInvolutionSquare
public import CFSG.LieType.Ree.LargeReeInvolutionCentralizers

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Ree.ReeTag

theorem card_vanishing (K : Type) [Field K] [Finite K] (Z : Finset (Fin 12)) :
    Nat.card {x : Fin 12 → K // ∀ i ∈ Z, x i = 0} = Nat.card K ^ (12 - Z.card) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let e : {x : Fin 12 → K // ∀ i ∈ Z, x i = 0} ≃ ({i : Fin 12 // i ∉ Z} → K) :=
    { toFun := fun x i => x.1 i
      invFun := fun y => ⟨fun i => if h : i ∈ Z then 0 else y ⟨i, h⟩, fun i hi => by simp [hi]⟩
      left_inv := fun x => Subtype.ext (funext fun i => by
        by_cases h : i ∈ Z
        · simp [h, x.2 i h]
        · simp [h])
      right_inv := fun y => funext fun i => by simp [i.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := {i : Fin 12 // i ∉ Z}),
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

section Centralizer

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem mem_image_sylowVec_iff
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (S : Set (Fin 12 → K)) {u : ModGL F4.tag K} :
    u ∈ sylowVec m K '' S ↔ u ∈ F4.reeFixedPosUnipotent K m ∧
      ∀ x : Fin 12 → K, sylowVec m K x = u → x ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(bijOn_sylowVec hK).1 (Set.mem_univ x), fun y hy => ?_⟩
    rwa [(bijOn_sylowVec hK).2.1 (Set.mem_univ y) (Set.mem_univ x) hy]
  · rintro ⟨hu, hS⟩
    obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    exact ⟨x, hS x rfl, rfl⟩

theorem card_image_sylowVec
    (hK : Nat.card K = 2 ^ (2 * m + 1)) (Z : Finset (Fin 12)) :
    Nat.card (sylowVec m K '' {x | ∀ i ∈ Z, x i = 0}) = (2 ^ (2 * m + 1)) ^ (12 - Z.card) := by
  rw [Nat.card_image_of_injOn ((bijOn_sylowVec hK).2.1.mono (Set.subset_univ _)), ← hK]
  exact card_vanishing K Z

theorem centralizer_sylowA_one
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 1 = 0 ∧ x 2 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0 ∧ x 9 = 0} := by
  ext u
  rw [mem_image_sylowVec_iff hK]
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hu, hc⟩ => ⟨hu, fun x hx => ?_⟩, fun ⟨hu, hS⟩ => ⟨hu, ?_⟩⟩
  · subst hx
    exact (sylowV_commute_sylowA_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hc
  · obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    exact (sylowV_commute_sylowA_one_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (hS x rfl)

theorem centralizer_sylowB_zero_one
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowB m K 0 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 0 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 10 = 0} := by
  ext u
  rw [mem_image_sylowVec_iff hK]
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hu, hc⟩ => ⟨hu, fun x hx => ?_⟩, fun ⟨hu, hS⟩ => ⟨hu, ?_⟩⟩
  · subst hx
    exact (sylowV_commute_sylowB_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hc
  · obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    exact (sylowV_commute_sylowB_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (hS x rfl)

theorem centralizer_sylowL_one
    (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowL m K 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 1 = 0 ∧ x 3 = 0} := by
  ext u
  rw [mem_image_sylowVec_iff hK]
  simp only [SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hu, hc⟩ => ⟨hu, fun x hx => ?_⟩, fun ⟨hu, hS⟩ => ⟨hu, ?_⟩⟩
  · subst hx
    exact (sylowV_commute_sylowL_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hc
  · obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    exact (sylowV_commute_sylowL_one_iff _ _ _ _ _ _ _ _ _ _ _ _).2 (hS x rfl)

theorem card_centralizer_of_eq
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    {H : Subgroup (ModGL F4.tag K)} {S : Set (Fin 12 → K)}
    (hH : (H : Set (ModGL F4.tag K)) = sylowVec m K '' S)
    (Z : Finset (Fin 12)) (hS : S = {x | ∀ i ∈ Z, x i = 0}) :
    Nat.card H = (2 ^ (2 * m + 1)) ^ (12 - Z.card) := by
  rw [← card_image_sylowVec hK Z, ← hS, ← hH]
  rfl

end Centralizer


theorem large_Ree_Sylow_involution_coordinate_reduction
    (m : ℕ) (K : Type)
    [Field K] [Finite K] [CharP K F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    (∀ s : K, largeReeSigma m (largeReeSigma m s) = s ^ 2) ∧
    Set.BijOn (sylowVec m K) Set.univ (F4.reeFixedPosUnipotent K m : Set (ModGL F4.tag K)) ∧
    (∀ a b c d e f g h i j k l : K, sylowV m K a b c d e f g h i j k l ^ 2 = 1 →
      b = 0 ∧ (a = 0 → d = 0)) ∧
    (∀ b c d e f g h i j k l : K, sylowV m K 1 b c d e f g h i j k l ^ 2 = 1 ↔
      b = 0 ∧ c = 0 ∧ h = f + d * largeReeSigma m d ∧ j = d * h + largeReeSigma m f ∧
        g = h * largeReeSigma m h + f * k + e * j + d * l + d * f * h + f * j +
          f * largeReeSigma m f + d * largeReeSigma m j) ∧
    (∀ b d e f g h i j k l : K, sylowV m K 0 b 1 d e f g h i j k l ^ 2 = 1 ↔
      b = 0 ∧ d = 0 ∧ h = largeReeSigma m f ∧ e = f * largeReeSigma m f ∧
        k = largeReeSigma m f * j) ∧
    (∀ b d e f g h i j k l : K, sylowV m K 0 b 0 d e f g h i j k l ^ 2 = 1 ↔
      b = 0 ∧ d = 0 ∧ f = 0 ∧ h = 0 ∧ e * j = 0) ∧
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 1 = 0 ∧ x 2 = 0 ∧ x 5 = 0 ∧ x 6 = 0 ∧ x 7 = 0 ∧ x 9 = 0} ∧
    Nat.card (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowA m K 1} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ 6 ∧
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowB m K 0 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 0 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 10 = 0} ∧
    Nat.card (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowB m K 0 1} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ 8 ∧
    (∀ u ∈ F4.reeFixedPosUnipotent K m,
      (∃ i : K, u * sylowB m K 0 1 * u⁻¹ = sylowB m K 0 1 * sylowH m K 0 i) →
        u * sylowB m K 0 1 * u⁻¹ = sylowB m K 0 1) ∧
    ((F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowL m K 1} :
        Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) =
      sylowVec m K '' {x | x 1 = 0 ∧ x 3 = 0} ∧
    Nat.card (F4.reeFixedPosUnipotent K m ⊓ Subgroup.centralizer {sylowL m K 1} :
      Subgroup (ModGL F4.tag K)) = (2 ^ (2 * m + 1)) ^ 10 := by
  refine ⟨largeReeSigma_sigma hK, bijOn_sylowVec hK, fun a b c d e f g h i j k l hv =>
    ⟨sq_eq_one_b hv, fun ha => ?_⟩, sylowV_one_sq_eq_one_iff hK,
    sylowV_zero_one_sq_eq_one_iff hK, sylowV_zero_zero_sq_eq_one_iff,
    centralizer_sylowA_one hK, card_centralizer_of_eq hK (centralizer_sylowA_one hK)
      {1, 2, 5, 6, 7, 9} (by ext x; simp), centralizer_sylowB_zero_one hK,
    card_centralizer_of_eq hK (centralizer_sylowB_zero_one hK) {0, 3, 4, 10} (by ext x; simp),
    fun u hu ⟨z, hz⟩ => ?_, centralizer_sylowL_one hK,
    card_centralizer_of_eq hK (centralizer_sylowL_one hK) {1, 3} (by ext x; simp)⟩
  · subst ha
    exact sq_eq_one_d hv
  · obtain ⟨x, -, rfl⟩ := (bijOn_sylowVec hK).2.2 hu
    exact sylowV_conj_eq_of_mem_mul _ _ _ _ _ _ _ _ _ _ _ _ z hz

end CFSG.LieType.Ree.LargeReeInvolution
