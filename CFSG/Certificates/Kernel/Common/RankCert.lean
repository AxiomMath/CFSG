module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.KC.RankCert

theorem rank_of_cert {n k : ℕ} (hk : k ≤ n) {M P Q : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hPQ : P * M = Q)
    (hQ : LinearIndependent (ZMod 2) (fun i : {i : Fin n // i.val < k} => Q i))
    (hQ0 : ∀ i : Fin n, k ≤ i.val → Q i = 0)
    (hP : LinearIndependent (ZMod 2) (fun i : {i : Fin n // k ≤ i.val} => P i)) :
    M.rank = k := by
  have hrow : ∀ i, M.vecMulLinear (P i) = Q i := by
    intro i
    rw [← hPQ]
    rfl
  have hrk : M.rank = Module.finrank (ZMod 2) (LinearMap.range M.vecMulLinear) := by
    rw [Matrix.rank_eq_finrank_span_row, range_vecMulLinear]
  have hlow : k ≤ Module.finrank (ZMod 2) (LinearMap.range M.vecMulLinear) := by
    have hli : LinearIndependent (ZMod 2) (fun i : {i : Fin n // i.val < k} =>
        (⟨Q i, P i, hrow i⟩ : LinearMap.range M.vecMulLinear)) :=
      LinearIndependent.of_comp (LinearMap.range M.vecMulLinear).subtype hQ
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin_lt_of_le hk] at this
  have hc : Fintype.card {i : Fin n // k ≤ i.val} = n - k := by
    have e : Fintype.card {i : Fin n // k ≤ i.val} = Fintype.card {i : Fin n // ¬ i.val < k} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => not_lt.symm)
    rw [e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin_lt_of_le hk]
  let A : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun i j => if k ≤ i.val then P i j else 0
  have hA : A * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    by_cases h : k ≤ i.val
    · have e := congrFun (hQ0 i h) j
      rw [← hPQ, Matrix.mul_apply] at e
      simpa [A, h] using e
    · simp [A, h]
  have hAr : n - k ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    have hmem : ∀ i : {i : Fin n // k ≤ i.val},
        P i ∈ Submodule.span (ZMod 2) (Set.range A.row) := by
      intro i
      have e : A.row i = P i := by
        funext j
        simp [A, Matrix.row, i.2]
      rw [← e]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hli : LinearIndependent (ZMod 2) (fun i : {i : Fin n // k ≤ i.val} =>
        (⟨P i, hmem i⟩ : Submodule.span (ZMod 2) (Set.range A.row))) :=
      LinearIndependent.of_comp (Submodule.span (ZMod 2) (Set.range A.row)).subtype hP
    have h := hli.fintype_card_le_finrank
    rwa [hc] at h
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hA
  rw [Fintype.card_fin] at hsum
  omega

end CFSG.KC.RankCert

end
