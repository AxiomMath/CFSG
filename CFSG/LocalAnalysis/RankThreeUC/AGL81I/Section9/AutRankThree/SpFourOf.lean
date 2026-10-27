module

public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix
open scoped MatrixGroups

theorem three_dvd_natCard_of_mul_mul {G : Type*} [Group G] {x : G} (h3 : x * x * x = 1)
    (h1 : x ≠ 1) : 3 ∣ Nat.card G :=
  orderOf_eq_prime (by rwa [pow_three']) h1 ▸ orderOf_dvd_natCard x

abbrev orderThreeMat (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, -1; 1, -1]

theorem orderThreeMat_mul_mul (R : Type*) [CommRing R] :
    orderThreeMat R * orderThreeMat R * orderThreeMat R = 1 := by
  rw [one_fin_two, mul_fin_two, mul_fin_two]
  simp

theorem orderThreeMat_ne_one (R : Type*) [CommRing R] [Nontrivial R] : orderThreeMat R ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

theorem three_dvd_card_SL_two (R : Type*) [CommRing R] [Nontrivial R] :
    3 ∣ Nat.card (SL(2, R)) := by
  let x : SL(2, R) := ⟨orderThreeMat R, by simp [det_fin_two]⟩
  refine three_dvd_natCard_of_mul_mul (x := x) ?_ ?_
  · exact Subtype.ext (orderThreeMat_mul_mul R)
  · intro h
    exact orderThreeMat_ne_one R (congrArg (fun y : SL(2, R) => (y : Matrix (Fin 2) (Fin 2) R)) h)

abbrev orderThreeMatDual (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![-1, -1; 1, 0]

theorem orderThreeMatDual_mul_mul (R : Type*) [CommRing R] :
    orderThreeMatDual R * orderThreeMatDual R * orderThreeMatDual R = 1 := by
  rw [one_fin_two, mul_fin_two, mul_fin_two]
  simp

theorem transpose_orderThreeMat_mul_dual (R : Type*) [CommRing R] :
    (orderThreeMat R)ᵀ * orderThreeMatDual R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_orderThreeMatDual_mul (R : Type*) [CommRing R] :
    (orderThreeMatDual R)ᵀ * orderThreeMat R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

abbrev spOrderThreeMat (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (orderThreeMat K) 0 0 (orderThreeMatDual K)

theorem spOrderThreeMat_mul_mul (K : Type) [Field K] :
    spOrderThreeMat K * spOrderThreeMat K * spOrderThreeMat K = 1 := by
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    orderThreeMat_mul_mul, orderThreeMatDual_mul_mul, fromBlocks_one]

theorem spOrderThreeMat_isometry (K : Type) [Field K] :
    (spOrderThreeMat K)ᵀ * fromBlocks 0 1 (-1) 0 * spOrderThreeMat K = fromBlocks 0 1 (-1) 0 := by
  simp only [fromBlocks_transpose, fromBlocks_multiply, transpose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    transpose_orderThreeMat_mul_dual, transpose_orderThreeMatDual_mul, neg_zero]

theorem three_dvd_card_statedSp_two (K : Type) [Field K] :
    3 ∣ Nat.card (CFSG.Open.StatedSp 2 K) := by
  have h := spOrderThreeMat_mul_mul K
  let u : GL (Fin 2 ⊕ Fin 2) K := ⟨spOrderThreeMat K, spOrderThreeMat K * spOrderThreeMat K,
    by rw [← Matrix.mul_assoc, h], h⟩
  let x : CFSG.Open.StatedSp 2 K := ⟨u, CFSG.Open.StatedAPI.mem_statedSp_iff.mpr
    (spOrderThreeMat_isometry K)⟩
  refine three_dvd_natCard_of_mul_mul (x := x) ?_ ?_
  · ext1
    ext1
    simpa [x, u] using h
  · intro hx
    have h1 := congrArg (fun y : CFSG.Open.StatedSp 2 K =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0)
        (Sum.inl 0)) hx
    simp [x, u] at h1

theorem three_dvd_card_of_quotient_center_alternatingGroup_seven {G : Type*} [Group G]
    (e : G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 7)) : 3 ∣ Nat.card G := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G),
    Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  exact Dvd.dvd.mul_right (by decide) _

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
