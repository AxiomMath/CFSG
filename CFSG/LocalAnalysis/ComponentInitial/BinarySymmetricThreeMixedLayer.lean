module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def binarySymThreeRankOne : Set ↥(binarySymMatrices 3) :=
  {B | (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1}

@[expose] def binarySymThreeAltNonzero : Set ↥(binarySymMatrices 3) :=
  {B | B ≠ 0 ∧ ∀ i, (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) i i = 0}

@[expose] def binarySymThreeDetOne : Set ↥(binarySymMatrices 3) :=
  {B | (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1}

@[expose] def binarySymThreeDetZero : Set ↥(binarySymMatrices 3) :=
  {B | (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 0}

@[expose] def binarySymThreeMixedX (S : Set ↥(binarySymMatrices 3)) :
    Set (↥(binarySymMatrices 3) × ZMod 2) :=
  {(0, 1)} ∪ S ×ˢ {1} ∪ binarySymThreeDetOne ×ˢ {0}

@[expose] def binarySymThreeMixedY (S : Set ↥(binarySymMatrices 3)) :
    Set (↥(binarySymMatrices 3) × ZMod 2) :=
  {(0, 1)} ∪ (S ∪ binarySymThreeDetOne) ×ˢ {1} ∪ binarySymThreeDetOne ×ˢ {0}

@[expose] def binarySymThreeMixedZ : Set (↥(binarySymMatrices 3) × ZMod 2) :=
  binarySymThreeDetZero ×ˢ {1} ∪ binarySymThreeDetOne ×ˢ {0}

@[expose] def binarySymThreeOne : ↥(binarySymMatrices 3) :=
  ⟨1, transpose_one⟩

@[expose] def binarySymThreeP₁ : ↥(binarySymMatrices 3) :=
  ⟨!![1, 0, 0; 0, 0, 0; 0, 0, 0], by decide⟩

@[expose] def binarySymThreeP₂ : ↥(binarySymMatrices 3) :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 0], by decide⟩

namespace BinarySymThreeMixed

@[expose] def rankOneDec (B : 𝕍) : Prop :=
  (Finset.univ.image (B : M₃).mulVec).card = 2

instance decidableRankOneDec : DecidablePred rankOneDec :=
  fun B => inferInstanceAs (Decidable ((Finset.univ.image (B : M₃).mulVec).card = 2))

@[expose] def altNonzeroDec (B : 𝕍) : Prop :=
  B ≠ 0 ∧ ∀ i, (B : M₃) i i = 0

instance decidableAltNonzeroDec : DecidablePred altNonzeroDec :=
  fun B => inferInstanceAs (Decidable (B ≠ 0 ∧ ∀ i, (B : M₃) i i = 0))

theorem rankOneDec_iff (B : 𝕍) : rankOneDec B ↔ B ∈ binarySymThreeRankOne :=
  (rank_eq_one_iff_card_image_mulVec _).symm

theorem altNonzeroDec_iff (B : 𝕍) : altNonzeroDec B ↔ B ∈ binarySymThreeAltNonzero :=
  Iff.rfl

@[expose] def xFinset (s : 𝕍 → Prop) [DecidablePred s] : Finset (𝕍 × ZMod 2) :=
  Finset.univ.filter fun p => (p = (0, 1) ∨ (s p.1 ∧ p.2 = 1)) ∨
    (binarySymDetThree (p.1 : M₃) = 1 ∧ p.2 = 0)

@[expose] def yFinset (s : 𝕍 → Prop) [DecidablePred s] : Finset (𝕍 × ZMod 2) :=
  Finset.univ.filter fun p => (p = (0, 1) ∨ ((s p.1 ∨ binarySymDetThree (p.1 : M₃) = 1) ∧
    p.2 = 1)) ∨ (binarySymDetThree (p.1 : M₃) = 1 ∧ p.2 = 0)

@[expose] def zFinset : Finset (𝕍 × ZMod 2) :=
  Finset.univ.filter fun p => (binarySymDetThree (p.1 : M₃) = 0 ∧ p.2 = 1) ∨
    (binarySymDetThree (p.1 : M₃) = 1 ∧ p.2 = 0)

theorem coe_xFinset (s : 𝕍 → Prop) [DecidablePred s] {S : Set 𝕍} (hs : ∀ B, s B ↔ B ∈ S) :
    (xFinset s : Set (𝕍 × ZMod 2)) = binarySymThreeMixedX S := by
  ext ⟨B, ε⟩
  simp only [xFinset, binarySymThreeMixedX, binarySymThreeDetOne, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.mem_union, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_ofPred_eq, hs, det_eq_binarySymDetThree B.2]

theorem coe_yFinset (s : 𝕍 → Prop) [DecidablePred s] {S : Set 𝕍} (hs : ∀ B, s B ↔ B ∈ S) :
    (yFinset s : Set (𝕍 × ZMod 2)) = binarySymThreeMixedY S := by
  ext ⟨B, ε⟩
  simp only [yFinset, binarySymThreeMixedY, binarySymThreeDetOne, Finset.coe_filter,
    Finset.mem_univ, true_and, Set.mem_union, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_ofPred_eq, hs, det_eq_binarySymDetThree B.2]

theorem coe_zFinset : (zFinset : Set (𝕍 × ZMod 2)) = binarySymThreeMixedZ := by
  ext ⟨B, ε⟩
  simp only [zFinset, binarySymThreeMixedZ, binarySymThreeDetOne, binarySymThreeDetZero,
    Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_prod, Set.mem_ofPred_eq, det_eq_binarySymDetThree B.2]

theorem card_x₁ : (xFinset rankOneDec).card = 36 := by decide +kernel
theorem card_x₂ : (xFinset altNonzeroDec).card = 36 := by decide +kernel
theorem card_y₁ : (yFinset rankOneDec).card = 64 := by decide +kernel
theorem card_y₂ : (yFinset altNonzeroDec).card = 64 := by decide +kernel
theorem card_z : zFinset.card = 64 := by decide +kernel

theorem t_x₁_z : ((((xFinset rankOneDec).erase (0, 1)).powersetCard 2).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 0 := by
  decide +kernel

theorem t_x₂_z : ((((xFinset altNonzeroDec).erase (0, 1)).powersetCard 2).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 0 := by
  decide +kernel

theorem t_z_z : (((zFinset.erase (0, 1)).powersetCard 2).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 0 := by
  decide +kernel

theorem t_x₁_one : 1 ≤ ((((xFinset rankOneDec).erase (binarySymThreeOne, 0)).powersetCard 2).filter
    fun Y => (binarySymThreeOne, (0 : ZMod 2)) + ∑ y ∈ Y, y = 0).card := by
  decide +kernel

theorem t_x₂_one : 1 ≤ ((((xFinset altNonzeroDec).erase (binarySymThreeOne, 0)).powersetCard
    2).filter fun Y => (binarySymThreeOne, (0 : ZMod 2)) + ∑ y ∈ Y, y = 0).card := by
  decide +kernel

theorem t_z_one : 1 ≤ (((zFinset.erase (binarySymThreeOne, 0)).powersetCard 2).filter fun Y =>
    (binarySymThreeOne, (0 : ZMod 2)) + ∑ y ∈ Y, y = 0).card := by
  decide +kernel

theorem t_y₁_z : ((((yFinset rankOneDec).erase (0, 1)).powersetCard 2).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 28 := by
  decide +kernel

theorem t_y₂_z : ((((yFinset altNonzeroDec).erase (0, 1)).powersetCard 2).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 28 := by
  decide +kernel

theorem t_y₁_p : ((((yFinset rankOneDec).erase (binarySymThreeP₁, 1)).powersetCard 2).filter
    fun Y => (binarySymThreeP₁, (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card ≤ 27 := by
  decide +kernel

theorem t_y₂_p : ((((yFinset altNonzeroDec).erase (binarySymThreeP₂, 1)).powersetCard 2).filter
    fun Y => (binarySymThreeP₂, (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card ≤ 27 := by
  decide +kernel

theorem card_image_mulVec_P₁ : (Finset.univ.image (binarySymThreeP₁ : M₃).mulVec).card = 2 := by
  decide +kernel

theorem altNonzeroDec_P₂ : altNonzeroDec binarySymThreeP₂ := by
  decide +kernel

theorem det_one' : (binarySymThreeOne : M₃).det = 1 :=
  det_one

end BinarySymThreeMixed

open BinarySymThreeMixed in
theorem binary_symmetric_three_mixed_layer_orbit_obstructions :
    (binarySymThreeMixedX binarySymThreeRankOne).ncard = 36 ∧
      (binarySymThreeMixedX binarySymThreeAltNonzero).ncard = 36 ∧
      (binarySymThreeMixedY binarySymThreeRankOne).ncard = 64 ∧
      (binarySymThreeMixedY binarySymThreeAltNonzero).ncard = 64 ∧
      binarySymThreeMixedZ.ncard = 64 ∧
      zeroSumIncidence (binarySymThreeMixedX binarySymThreeRankOne) 3 (0, 1) = 0 ∧
      zeroSumIncidence (binarySymThreeMixedX binarySymThreeAltNonzero) 3 (0, 1) = 0 ∧
      zeroSumIncidence binarySymThreeMixedZ 3 (0, 1) = 0 ∧
      1 ≤ zeroSumIncidence (binarySymThreeMixedX binarySymThreeRankOne) 3
        (binarySymThreeOne, 0) ∧
      1 ≤ zeroSumIncidence (binarySymThreeMixedX binarySymThreeAltNonzero) 3
        (binarySymThreeOne, 0) ∧
      1 ≤ zeroSumIncidence binarySymThreeMixedZ 3 (binarySymThreeOne, 0) ∧
      zeroSumIncidence (binarySymThreeMixedY binarySymThreeRankOne) 3 (0, 1) = 28 ∧
      zeroSumIncidence (binarySymThreeMixedY binarySymThreeAltNonzero) 3 (0, 1) = 28 ∧
      zeroSumIncidence (binarySymThreeMixedY binarySymThreeRankOne) 3
        (binarySymThreeP₁, 1) ≤ 27 ∧
      zeroSumIncidence (binarySymThreeMixedY binarySymThreeAltNonzero) 3
        (binarySymThreeP₂, 1) ≤ 27 ∧
      ∀ Λ ∈ ({binarySymThreeMixedX binarySymThreeRankOne,
          binarySymThreeMixedX binarySymThreeAltNonzero,
          binarySymThreeMixedY binarySymThreeRankOne,
          binarySymThreeMixedY binarySymThreeAltNonzero,
          binarySymThreeMixedZ} : Set (Set (↥(binarySymMatrices 3) × ZMod 2))),
        ∀ (G : Type*) [Group G] [DistribMulAction G (↥(binarySymMatrices 3) × ZMod 2)],
          (∀ g : G, (fun x => g • x) '' Λ = Λ) →
            ¬ ∀ p ∈ Λ, ∀ q ∈ Λ, ∃ g : G, g • p = q := by
  have hX₁ := coe_xFinset rankOneDec rankOneDec_iff
  have hX₂ := coe_xFinset altNonzeroDec altNonzeroDec_iff
  have hY₁ := coe_yFinset rankOneDec rankOneDec_iff
  have hY₂ := coe_yFinset altNonzeroDec altNonzeroDec_iff
  have hzX : ∀ S : Set 𝕍, ((0, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedX S :=
    fun _ => Or.inl (Or.inl rfl)
  have hzY : ∀ S : Set 𝕍, ((0, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedY S :=
    fun _ => Or.inl (Or.inl rfl)
  have hzZ : ((0, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedZ := Or.inl ⟨det_zero, rfl⟩
  have hoX : ∀ S : Set 𝕍, ((binarySymThreeOne, 0) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedX S :=
    fun _ => Or.inr ⟨det_one', rfl⟩
  have hoZ : ((binarySymThreeOne, 0) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedZ :=
    Or.inr ⟨det_one', rfl⟩
  have hp₁ : ((binarySymThreeP₁, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedY binarySymThreeRankOne :=
    Or.inl (Or.inr ⟨Or.inl ((rank_eq_one_iff_card_image_mulVec _).2 card_image_mulVec_P₁), rfl⟩)
  have hp₂ :
      ((binarySymThreeP₂, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeMixedY binarySymThreeAltNonzero :=
    Or.inl (Or.inr ⟨Or.inl altNonzeroDec_P₂, rfl⟩)
  have e1 : zeroSumIncidence (binarySymThreeMixedX binarySymThreeRankOne) 3 (0, 1) = 0 := by
    rw [zeroSumIncidence_eq_card_erase _ hX₁ (k := 3) (by norm_num) (hzX _)]
    exact t_x₁_z
  have e2 : zeroSumIncidence (binarySymThreeMixedX binarySymThreeAltNonzero) 3 (0, 1) = 0 := by
    rw [zeroSumIncidence_eq_card_erase _ hX₂ (k := 3) (by norm_num) (hzX _)]
    exact t_x₂_z
  have e3 : zeroSumIncidence binarySymThreeMixedZ 3 (0, 1) = 0 := by
    rw [zeroSumIncidence_eq_card_erase _ coe_zFinset (k := 3) (by norm_num) hzZ]
    exact t_z_z
  have e4 : 1 ≤ zeroSumIncidence (binarySymThreeMixedX binarySymThreeRankOne) 3
      (binarySymThreeOne, 0) := by
    rw [zeroSumIncidence_eq_card_erase _ hX₁ (k := 3) (by norm_num) (hoX _)]
    exact t_x₁_one
  have e5 : 1 ≤ zeroSumIncidence (binarySymThreeMixedX binarySymThreeAltNonzero) 3
      (binarySymThreeOne, 0) := by
    rw [zeroSumIncidence_eq_card_erase _ hX₂ (k := 3) (by norm_num) (hoX _)]
    exact t_x₂_one
  have e6 : 1 ≤ zeroSumIncidence binarySymThreeMixedZ 3 (binarySymThreeOne, 0) := by
    rw [zeroSumIncidence_eq_card_erase _ coe_zFinset (k := 3) (by norm_num) hoZ]
    exact t_z_one
  have e7 : zeroSumIncidence (binarySymThreeMixedY binarySymThreeRankOne) 3 (0, 1) = 28 := by
    rw [zeroSumIncidence_eq_card_erase _ hY₁ (k := 3) (by norm_num) (hzY _)]
    exact t_y₁_z
  have e8 : zeroSumIncidence (binarySymThreeMixedY binarySymThreeAltNonzero) 3 (0, 1) = 28 := by
    rw [zeroSumIncidence_eq_card_erase _ hY₂ (k := 3) (by norm_num) (hzY _)]
    exact t_y₂_z
  have e9 : zeroSumIncidence (binarySymThreeMixedY binarySymThreeRankOne) 3
      (binarySymThreeP₁, 1) ≤ 27 := by
    rw [zeroSumIncidence_eq_card_erase _ hY₁ (k := 3) (by norm_num) hp₁]
    exact t_y₁_p
  have e10 : zeroSumIncidence (binarySymThreeMixedY binarySymThreeAltNonzero) 3
      (binarySymThreeP₂, 1) ≤ 27 := by
    rw [zeroSumIncidence_eq_card_erase _ hY₂ (k := 3) (by norm_num) hp₂]
    exact t_y₂_p
  refine ⟨?_, ?_, ?_, ?_, ?_, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, ?_⟩
  · rw [← hX₁, Set.ncard_coe_finset, card_x₁]
  · rw [← hX₂, Set.ncard_coe_finset, card_x₂]
  · rw [← hY₁, Set.ncard_coe_finset, card_y₁]
  · rw [← hY₂, Set.ncard_coe_finset, card_y₂]
  · rw [← coe_zFinset, Set.ncard_coe_finset, card_z]
  · intro Λ hΛ G _ _ hG
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hΛ
    rcases hΛ with rfl | rfl | rfl | rfl | rfl
    · exact not_transitive_of_zeroSumIncidence_ne (k := 3) (hzX _) (hoX _) (by omega) G hG
    · exact not_transitive_of_zeroSumIncidence_ne (k := 3) (hzX _) (hoX _) (by omega) G hG
    · exact not_transitive_of_zeroSumIncidence_ne (k := 3) (hzY _) hp₁ (by omega) G hG
    · exact not_transitive_of_zeroSumIncidence_ne (k := 3) (hzY _) hp₂ (by omega) G hG
    · exact not_transitive_of_zeroSumIncidence_ne (k := 3) hzZ hoZ (by omega) G hG

end CFSG.LocalAnalysis.ComponentInitial
