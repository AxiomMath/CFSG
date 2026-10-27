module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Matrix

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def binarySymThreeFifteenSet : Set (↥(binarySymMatrices 3) × ZMod 2) :=
  {p | p.2 = 1 ∧ ((p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∈ binaryAltMatrices 3 ∨
    (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1)}

namespace BinarySymThreeFifteen

@[expose] def fifteenFinset : Finset (𝕍 × ZMod 2) :=
  Finset.univ.filter fun p => p.2 = 1 ∧
    ((p.1 : M₃) ∈ binaryAltMatrices 3 ∨ (Finset.univ.image (p.1 : M₃).mulVec).card = 2)

theorem coe_fifteenFinset : (fifteenFinset : Set (𝕍 × ZMod 2)) = binarySymThreeFifteenSet := by
  ext p
  simp [fifteenFinset, binarySymThreeFifteenSet, rank_eq_one_iff_card_image_mulVec]

theorem card_fifteenFinset : fifteenFinset.card = 15 := by
  decide +kernel

theorem card_zero : (((fifteenFinset.erase (0, 1)).powersetCard 3).filter fun Y =>
    ((0 : 𝕍), (1 : ZMod 2)) + ∑ y ∈ Y, y = 0).card = 7 := by
  decide +kernel

theorem card_rankOne : ∀ B : 𝕍, (Finset.univ.image (B : M₃).mulVec).card = 2 →
    (((fifteenFinset.erase (B, 1)).powersetCard 3).filter fun Y =>
      ((B, 1) : 𝕍 × ZMod 2) + ∑ y ∈ Y, y = 0).card = 3 := by
  decide +kernel

@[expose] def symE₁₁ : 𝕍 :=
  ⟨!![1, 0, 0; 0, 0, 0; 0, 0, 0], by decide⟩

theorem card_image_mulVec_symE₁₁ : (Finset.univ.image (symE₁₁ : M₃).mulVec).card = 2 := by
  decide +kernel

theorem add_self_eq_zero' (a : 𝕍 × ZMod 2) : a + a = 0 :=
  Prod.ext (Subtype.ext (binary_add_self _)) (CharTwo.add_self_eq_zero _)

theorem four_nsmul (a : 𝕍 × ZMod 2) : 4 • a = 0 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul, add_self_eq_zero']

end BinarySymThreeFifteen

open BinarySymThreeFifteen in
theorem binary_symmetric_three_fifteen_point_linear_orbit_obstruction :
    binarySymThreeFifteenSet.ncard = 15 ∧
      zeroSumIncidence binarySymThreeFifteenSet 4 (0, 1) = 7 ∧
      (∀ B : ↥(binarySymMatrices 3), (B : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 →
        zeroSumIncidence binarySymThreeFifteenSet 4 (B, 1) = 3) ∧
      (¬ ∀ p ∈ binarySymThreeFifteenSet, ∀ p' ∈ binarySymThreeFifteenSet,
        ∃ (g : (↥(binarySymMatrices 3) × ZMod 2) ≃+ (↥(binarySymMatrices 3) × ZMod 2))
          (a : ↥(binarySymMatrices 3) × ZMod 2),
          (fun x => g x + a) '' binarySymThreeFifteenSet = binarySymThreeFifteenSet ∧
            g p + a = p') ∧
      ∀ (G : Type*) [Group G] [DistribMulAction G (↥(binarySymMatrices 3) × ZMod 2)],
        (∀ g : G, (fun x => g • x) '' binarySymThreeFifteenSet = binarySymThreeFifteenSet) →
          ¬ ∀ p ∈ binarySymThreeFifteenSet, ∀ p' ∈ binarySymThreeFifteenSet,
            ∃ g : G, g • p = p' := by
  have hq0 : zeroSumIncidence binarySymThreeFifteenSet 4 (0, 1) = 7 := by
    have hp : ((0, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeFifteenSet := ⟨rfl, Or.inl (zero_mem _)⟩
    rw [zeroSumIncidence_eq_card_erase _ coe_fifteenFinset (k := 4) (by norm_num) hp]
    exact card_zero
  have hq1 : ∀ B : 𝕍, (B : M₃).rank = 1 →
      zeroSumIncidence binarySymThreeFifteenSet 4 (B, 1) = 3 := by
    intro B hB
    have hp : ((B, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeFifteenSet := ⟨rfl, Or.inr hB⟩
    rw [zeroSumIncidence_eq_card_erase _ coe_fifteenFinset (k := 4) (by norm_num) hp]
    exact card_rankOne B ((rank_eq_one_iff_card_image_mulVec _).1 hB)
  have haff : ¬ ∀ p ∈ binarySymThreeFifteenSet, ∀ p' ∈ binarySymThreeFifteenSet,
      ∃ (g : (𝕍 × ZMod 2) ≃+ (𝕍 × ZMod 2)) (a : 𝕍 × ZMod 2),
        (fun x => g x + a) '' binarySymThreeFifteenSet = binarySymThreeFifteenSet ∧
          g p + a = p' := by
    intro h
    have hE : (symE₁₁ : M₃).rank = 1 :=
      (rank_eq_one_iff_card_image_mulVec _).2 card_image_mulVec_symE₁₁
    have hp : ((0, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeFifteenSet := ⟨rfl, Or.inl (zero_mem _)⟩
    have hp' : ((symE₁₁, 1) : 𝕍 × ZMod 2) ∈ binarySymThreeFifteenSet := ⟨rfl, Or.inr hE⟩
    obtain ⟨g, a, hΩ, hga⟩ := h _ hp _ hp'
    have hq := zeroSumIncidence_affine g (add_self_eq_zero' a) hΩ (four_nsmul a) (0, 1)
    rw [hga, hq1 symE₁₁ hE, hq0] at hq
    exact absurd hq (by norm_num)
  refine ⟨?_, hq0, hq1, haff, fun G _ _ hG htrans => haff fun p hp p' hp' => ?_⟩
  · rw [← coe_fifteenFinset, Set.ncard_coe_finset, card_fifteenFinset]
  · obtain ⟨g, hg⟩ := htrans p hp p' hp'
    refine ⟨DistribMulAction.toAddEquiv _ g, 0, ?_, ?_⟩
    · simpa only [DistribMulAction.toAddEquiv_apply, add_zero] using hG g
    · rw [DistribMulAction.toAddEquiv_apply, add_zero, hg]

end CFSG.LocalAnalysis.ComponentInitial
