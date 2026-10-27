module

public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

@[expose] noncomputable def fixCount (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) : ℕ :=
  Nat.card {w : Fin 24 → ZMod 2 // M *ᵥ w = w}

@[expose] def subOneRows (R : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 24) fun i => (R[i.val]?.getD 0) ^^^ (1 <<< i.val)

@[expose] def diagRows (r : ℕ) : Array ℕ :=
  Array.ofFn (n := 24) fun i => if i.val < r then 1 <<< i.val else 0

@[expose] def fixCheck (R P Q : Array ℕ) (r : ℕ) : Bool :=
  mulRows 24 (mulRows 24 P (subOneRows R)) Q == diagRows r

theorem rowsMatrix_subOneRows (R : Array ℕ) :
    rowsMatrix 24 (subOneRows R) = rowsMatrix 24 R - 1 := by
  ext i j
  rw [rowsMatrix_apply, Matrix.sub_apply, rowsMatrix_apply, Matrix.one_apply]
  unfold subOneRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  rw [toVecD_xor, Pi.add_apply, Nat.one_shiftLeft]
  have h1 : toVecD 24 (2 ^ i.val) j = if i = j then 1 else 0 := by
    rw [toVecD_apply, Nat.testBit_two_pow]
    by_cases h : i = j
    · subst h
      simp
    · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
      simp [h, h']
  rw [h1]
  exact (CharTwo.sub_eq_add _ _).symm

theorem rowsMatrix_diagRows (r : ℕ) :
    rowsMatrix 24 (diagRows r) =
      Matrix.diagonal (fun i : Fin 24 => if i.val < r then (1 : ZMod 2) else 0) := by
  ext i j
  rw [rowsMatrix_apply]
  unfold diagRows
  simp only [Array.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
  by_cases hr : i.val < r
  · simp only [hr, if_true]
    rw [Nat.one_shiftLeft, toVecD_apply, Nat.testBit_two_pow, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp [hr]
    · have h' : i.val ≠ j.val := fun e => h (Fin.ext e)
      simp [h, h']
  · simp [hr, toVecD_zero, Matrix.diagonal_apply]

theorem rank_diag_ones {r : ℕ} (hr : r ≤ 24) :
    (Matrix.diagonal (fun i : Fin 24 => if i.val < r then (1 : ZMod 2) else 0)).rank = r := by
  rw [Matrix.rank_diagonal]
  have e : Fintype.card {i : Fin 24 // (if i.val < r then (1 : ZMod 2) else 0) ≠ 0} =
      Fintype.card {i : Fin 24 // i.val < r} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
      by_cases h : i.val < r <;> simp [h])
  exact e.trans (Fintype.card_fin_lt_of_le hr)

theorem card_fixed_le_of_rank {K : Type} [Field K] [Finite K] {M : Matrix (Fin 24) (Fin 24) K}
    {r : ℕ} (h : r ≤ (M - 1).rank) :
    Nat.card {w : Fin 24 → K // M *ᵥ w = w} ≤ Nat.card K ^ (24 - r) := by
  have e : {w : Fin 24 → K // M *ᵥ w = w} ≃ LinearMap.ker (M - 1).mulVecLin :=
    Equiv.subtypeEquivRight fun w => by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
        sub_eq_zero]
  have h5 := LinearMap.finrank_range_add_finrank_ker (M - 1).mulVecLin
  rw [Module.finrank_fin_fun] at h5
  have h6 : (M - 1).rank = Module.finrank K (LinearMap.range (M - 1).mulVecLin) := rfl
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K)]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem fixCount_le_of_rank {M : Matrix (Fin 24) (Fin 24) (ZMod 2)} {r : ℕ}
    (h : r ≤ (M - 1).rank) : fixCount M ≤ 2 ^ (24 - r) := by
  have := card_fixed_le_of_rank (K := ZMod 2) (M := M) h
  rwa [Nat.card_zmod] at this

theorem card_fixed_le_of_fixCheck {R P Q : Array ℕ} {r : ℕ} (hr : r ≤ 24)
    (h : fixCheck R P Q r = true) : fixCount (rowsMatrix 24 R) ≤ 2 ^ (24 - r) := by
  have h1 : mulRows 24 (mulRows 24 P (subOneRows R)) Q = diagRows r := by
    simpa [fixCheck] using h
  have h2 := congrArg (rowsMatrix 24) h1
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_subOneRows, rowsMatrix_diagRows] at h2
  refine fixCount_le_of_rank ?_
  have h4 := congrArg Matrix.rank h2
  rw [rank_diag_ones hr] at h4
  rw [← h4]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end CFSG.HardMathSupport.Dickson.I271.TabMFive
