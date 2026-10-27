module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

public section

namespace CFSG.ClassicalGroups.Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem det_id_add_smulRight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) {c : V} {θ : Module.Dual K V} (hθ : θ c = 0) :
    LinearMap.det (LinearMap.id + LinearMap.smulRight θ c) = 1 := by
  rw [← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b b (LinearMap.id + LinearMap.smulRight θ c) =
      1 + Matrix.replicateCol Unit (fun i => b.repr c i) *
        Matrix.replicateRow Unit (fun j => θ (b j)) := by
    ext i j
    simp [LinearMap.toMatrix_apply, Matrix.mul_apply, Matrix.one_apply, Finsupp.single_apply,
      mul_comm, eq_comm]
  have hsum : dotProduct (fun j => θ (b j)) (fun i => b.repr c i) = θ c := by
    have h := congrArg θ (b.sum_repr c)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    rw [← h]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow, hsum, hθ, add_zero]

end CFSG.ClassicalGroups.Linear
