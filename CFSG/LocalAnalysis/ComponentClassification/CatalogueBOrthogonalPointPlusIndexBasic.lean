module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryIndex
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryPolar

public section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex

open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalPointAction

universe u

@[expose] def pointIndex (q n : ℕ) : ℕ :=
  ((q ^ n - 1) * (q ^ (n - 1) + 1)) / (q - 1)

theorem splitCount_point_formula (q n : ℕ) :
    splitCount q n 1 =
      (((q : ℚ) ^ n - 1) * ((q : ℚ) ^ (n - 1) + 1)) / ((q : ℚ) - 1) := by
  simp [splitCount]

theorem nat_eq_pointIndex_of_splitCount (q n i : ℕ) (hq : 2 ≤ q)
    (hi : (i : ℚ) = splitCount q n 1) : i = pointIndex q n := by
  have hqQ : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have hden : (q : ℚ) - 1 ≠ 0 := by linarith
  have hpow : 1 ≤ q ^ n := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) n)
  have hmul : (i : ℚ) * ((q : ℚ) - 1) =
      ((q : ℚ) ^ n - 1) * ((q : ℚ) ^ (n - 1) + 1) := by
    rw [hi, splitCount_point_formula, div_mul_cancel₀ _ hden]
  have hnat : i * (q - 1) = (q ^ n - 1) * (q ^ (n - 1) + 1) := by
    apply Nat.cast_injective (R := ℚ)
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_sub hpow,
      Nat.cast_one, Nat.cast_add, Nat.cast_pow]
    exact hmul
  exact Nat.eq_div_of_mul_eq_left (by omega) hnat

variable {K : Type u} [Field K] [Finite K] {n : ℕ}

theorem split_point_stabilizer_index (hn : 3 ≤ n) (L : Points (quadPlus n K)) :
    (MulAction.stabilizer (splitProj n K) L.val).index = pointIndex (Nat.card K) n := by
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hi := (orthogonal_geometry_split_geometric_stabilizer_indices hn L.property.2).1
    (by rw [L.property.1]; omega)
  exact nat_eq_pointIndex_of_splitCount _ _ _ hq (by simpa only [L.property.1] using hi)

theorem split_intermediate_index_gt_point (hn : 3 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) (hW : ∀ v ∈ W, quadPlus n K v = 0)
    (hW2 : 2 ≤ Module.finrank K W) (hWn : Module.finrank K W < n)
    (L : Points (quadPlus n K)) :
    (MulAction.stabilizer (splitProj n K) L.val).index <
      (MulAction.stabilizer (splitProj n K) W).index := by
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcount := orthogonal_geometry_split_count_comparison hq hn
  have hL := (orthogonal_geometry_split_geometric_stabilizer_indices hn L.property.2).1
    (by rw [L.property.1]; omega)
  have hWi := (orthogonal_geometry_split_geometric_stabilizer_indices hn hW).1 hWn
  have hlt : ((MulAction.stabilizer (splitProj n K) L.val).index : ℚ) <
      ((MulAction.stabilizer (splitProj n K) W).index : ℚ) := by
    rw [hL, L.property.1, hWi]
    exact hcount.2.2.2.1 _ hW2 (by omega)
  exact_mod_cast hlt

theorem split_high_rank_index_gt_point (hn : 5 ≤ n)
    (W : Submodule K (Fin n ⊕ Fin n → K)) (hW : ∀ v ∈ W, quadPlus n K v = 0)
    (hW2 : 2 ≤ Module.finrank K W) (L : Points (quadPlus n K)) :
    (MulAction.stabilizer (splitProj n K) L.val).index <
      (MulAction.stabilizer (splitProj n K) W).index := by
  have hr : 3 ≤ n := by omega
  have hdim := finrank_le_of_totSing hW
  rcases lt_or_eq_of_le hdim with hlt | heq
  · exact split_intermediate_index_gt_point hr W hW hW2 hlt L
  · have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
    have hcount := orthogonal_geometry_split_count_comparison hq hr
    have hL := (orthogonal_geometry_split_geometric_stabilizer_indices hr L.property.2).1
      (by rw [L.property.1]; omega)
    have hWi := (orthogonal_geometry_split_geometric_stabilizer_indices hr hW).2 heq
    have hlt : ((MulAction.stabilizer (splitProj n K) L.val).index : ℚ) <
        ((MulAction.stabilizer (splitProj n K) W).index : ℚ) := by
      rw [hL, L.property.1, hWi]
      exact (hcount.2.2.2.2.2 hn).1
    exact_mod_cast hlt

theorem split_four_maximal_index_eq_point
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) (hW : ∀ v ∈ W, quadPlus 4 K v = 0)
    (hW4 : Module.finrank K W = 4) (L : Points (quadPlus 4 K)) :
    (MulAction.stabilizer (splitProj 4 K) W).index =
      (MulAction.stabilizer (splitProj 4 K) L.val).index := by
  have hq : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hcount := orthogonal_geometry_split_count_comparison hq (by omega : 3 ≤ 4)
  have hL := (orthogonal_geometry_split_geometric_stabilizer_indices (by omega : 3 ≤ 4)
    L.property.2).1 (by rw [L.property.1]; omega)
  have hWi := (orthogonal_geometry_split_geometric_stabilizer_indices (by omega : 3 ≤ 4) hW).2 hW4
  apply Nat.cast_injective (R := ℚ)
  rw [hWi, hL, L.property.1]
  exact hcount.2.2.2.2.1

theorem split_four_intermediate_index_gt_point
    (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) (hW : ∀ v ∈ W, quadPlus 4 K v = 0)
    (hW23 : Module.finrank K W = 2 ∨ Module.finrank K W = 3)
    (L : Points (quadPlus 4 K)) :
    (MulAction.stabilizer (splitProj 4 K) L.val).index <
      (MulAction.stabilizer (splitProj 4 K) W).index :=
  split_intermediate_index_gt_point (by omega) W hW (by omega) (by omega) L

end CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusIndex
