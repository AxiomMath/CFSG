module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Labels
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFifteenPoint
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeMixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeSingularSet

public section

namespace CFSG.EvenSmallLie.Child3

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

local notation "𝕍" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}
local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem ne_zero_iff_kindOf (B : 𝕍) : B ≠ 0 ↔ kindOf B ≠ 0 := by
  rw [Ne, Ne, kindOf_eq_zero_iff]

theorem eq_zero_iff_kindOf (B : 𝕍) : B = 0 ↔ kindOf B = 0 :=
  (kindOf_eq_zero_iff B).symm

theorem rank_one_iff_kindOf (B : 𝕍) : (B : M₃).rank = 1 ↔ kindOf B = 1 :=
  (kindOf_eq_one_iff B).symm

theorem patternSet_fifteen : patternSet {0, 1} = binarySymThreeFifteenSet := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  change _ ↔ ε = 1 ∧ ((B : M₃) ∈ binaryAltMatrices 3 ∨ (B : M₃).rank = 1)
  dsimp only
  rw [mem_binaryAltMatrices_iff, alt_iff_kindOf, rank_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_X₁ : patternSet {0, 4} = binarySymThreeMixedX binarySymThreeRankOne := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [binarySymThreeMixedX, binarySymThreeRankOne, binarySymThreeDetOne, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq, Prod.mk.injEq]
  rw [eq_zero_iff_kindOf, rank_one_iff_kindOf, det_eq_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_X₂ : patternSet {1, 4} = binarySymThreeMixedX binarySymThreeAltNonzero := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [binarySymThreeMixedX, binarySymThreeAltNonzero, binarySymThreeDetOne,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq, Prod.mk.injEq]
  rw [eq_zero_iff_kindOf, ne_zero_iff_kindOf, alt_iff_kindOf, det_eq_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_Y₁ : patternSet {0, 3, 4} = binarySymThreeMixedY binarySymThreeRankOne := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [binarySymThreeMixedY, binarySymThreeRankOne, binarySymThreeDetOne, Set.mem_union,
    Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq, Prod.mk.injEq]
  rw [eq_zero_iff_kindOf, rank_one_iff_kindOf, det_eq_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_Y₂ :
    patternSet {1, 3, 4} = binarySymThreeMixedY binarySymThreeAltNonzero := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [binarySymThreeMixedY, binarySymThreeAltNonzero, binarySymThreeDetOne,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_prod, Set.mem_ofPred_eq, Prod.mk.injEq]
  rw [eq_zero_iff_kindOf, ne_zero_iff_kindOf, alt_iff_kindOf, det_eq_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_Z : patternSet {0, 1, 2, 4} = binarySymThreeMixedZ := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  simp only [binarySymThreeMixedZ, binarySymThreeDetZero, binarySymThreeDetOne, Set.mem_union,
    Set.mem_prod, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [det_eq_zero_iff_kindOf, det_eq_one_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

theorem patternSet_singular : patternSet {0, 1, 2} = binarySymThreeSingularShift := by
  ext ⟨B, ε⟩
  rw [mem_patternSet_iff]
  change _ ↔ ε = 1 ∧ (B : M₃).det = 0
  dsimp only
  rw [det_eq_zero_iff_kindOf]
  generalize kindOf B = k
  revert k ε
  decide

end CFSG.EvenSmallLie.Child3
