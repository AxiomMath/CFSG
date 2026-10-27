module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import TauCeti.Algebra.BigOperators.ZPow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

theorem zpow_det_eq_one_of_prod_zpow_eq_one {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommGroup M] {A : Matrix ι ι ℤ} {x : ι → M} (hx : ∀ j, ∏ i, x i ^ A i j = 1) (j : ι) :
    x j ^ A.det = 1 := by
  have h1 : (∏ k, (∏ i, x i ^ A i k) ^ A.adjugate k j) = x j ^ A.det := by
    calc ∏ k, (∏ i, x i ^ A i k) ^ A.adjugate k j
        = ∏ k, ∏ i, x i ^ (A i k * A.adjugate k j) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [← Finset.prod_zpow]
          exact Finset.prod_congr rfl fun i _ => (zpow_mul _ _ _).symm
      _ = ∏ i, ∏ k, x i ^ (A i k * A.adjugate k j) := Finset.prod_comm
      _ = ∏ i, x i ^ (∑ k, A i k * A.adjugate k j) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [Finset.prod_zpow_eq_zpow_sum]
      _ = ∏ i, x i ^ ((A * A.adjugate) i j) := by
          simp only [Matrix.mul_apply]
      _ = ∏ i, x i ^ (A.det * (1 : Matrix ι ι ℤ) i j) := by
          rw [Matrix.mul_adjugate]
          simp
      _ = x j ^ A.det := by
          rw [Finset.prod_eq_single j]
          · rw [Matrix.one_apply_eq, mul_one]
          · intro i _ hi
            rw [Matrix.one_apply_ne hi, mul_zero, zpow_zero]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
  rw [← h1]
  exact Finset.prod_eq_one fun k _ => by rw [hx k, one_zpow]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
