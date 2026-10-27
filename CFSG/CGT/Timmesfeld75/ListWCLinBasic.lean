module

public import CFSG.CGT.Timmesfeld75.SLTransvection
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.CGT.Timmesfeld75

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K] {m : ℕ}

theorem exists_smul_of_vecMulVec_eq {u v u' v' : Fin m → K}
    (h : vecMulVec u v = vecMulVec u' v') (hu' : u' ≠ 0) (hv : v ≠ 0) :
    ∃ μ : K, u = μ • u' ∧ v' = μ • v := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu'
  have hj' : v j ≠ 0 := by simpa using hj
  have hi' : u' i ≠ 0 := by simpa using hi
  have hij : ∀ a b, u a * v b = u' a * v' b := fun a b => by
    have := congrFun₂ h a b
    simpa [vecMulVec_apply] using this
  have hu : ∀ a, u a = v' j / v j * u' a := fun a => by
    rw [div_mul_eq_mul_div, eq_div_iff hj', hij a j, mul_comm]
  refine ⟨v' j / v j, funext fun a => by simp only [Pi.smul_apply, smul_eq_mul, hu a],
    funext fun b => ?_⟩
  have h1 := hij i b
  rw [hu i] at h1
  have h3 : u' i * (v' j / v j * v b) = u' i * v' b := by rw [← h1]; ring
  simp only [Pi.smul_apply, smul_eq_mul]
  exact (mul_left_cancel₀ hi' h3).symm

theorem vecMulVec_ne_zero_of {u v : Fin m → K} (hu : u ≠ 0) (hv : v ≠ 0) : vecMulVec u v ≠ 0 :=
  fun h => (vecMulVec_eq_zero.1 h).elim hu hv

theorem det_one_add_vecMulVec_of_dot {c a : Fin m → K} (h : a ⬝ᵥ c = 0) :
    (1 + vecMulVec c a).det = 1 := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]

@[expose] def tvSL (c a : Fin m → K) (h : a ⬝ᵥ c = 0) : SL(m, K) :=
  ⟨1 + vecMulVec c a, det_one_add_vecMulVec_of_dot h⟩

theorem coe_tvSL {c a : Fin m → K} (h : a ⬝ᵥ c = 0) :
    ((tvSL c a h : SL(m, K)) : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a :=
  rfl

theorem coe_mul_coe_inv' (g : SL(m, K)) :
    (g : Matrix (Fin m) (Fin m) K) * ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_mul_coe' (g : SL(m, K)) :
    ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) * (g : Matrix (Fin m) (Fin m) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_inv_eq_of_mul_eq_one {g : SL(m, K)} {M : Matrix (Fin m) (Fin m) K}
    (h : (g : Matrix (Fin m) (Fin m) K) * M = 1) :
    ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) = M := by
  calc ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)
      = ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) * ((g : Matrix (Fin m) (Fin m) K) * M) := by
        rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, coe_inv_mul_coe', Matrix.one_mul]

theorem coe_tvSL_inv {c a : Fin m → K} (h : a ⬝ᵥ c = 0) :
    (((tvSL c a h)⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) = 1 - vecMulVec c a := by
  apply coe_inv_eq_of_mul_eq_one
  rw [coe_tvSL, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, vecMulVec_mul_vecMulVec, h, zero_smul, vecMulVec_zero]
  abel

theorem coe_conj_of_coe (g : SL(m, K)) {x : SL(m, K)} {c a : Fin m → K}
    (hx : (x : Matrix (Fin m) (Fin m) K) = 1 + vecMulVec c a) :
    ((g * x * g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) =
      1 + vecMulVec ((g : Matrix (Fin m) (Fin m) K) *ᵥ c)
        (a ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_one, coe_mul_coe_inv', mul_vecMulVec, vecMulVec_mul]

theorem inv_mulVec_mulVec' (g : SL(m, K)) (v : Fin m → K) :
    ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ ((g : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := by
  rw [mulVec_mulVec, coe_inv_mul_coe', one_mulVec]

theorem mulVec_inv_mulVec' (g : SL(m, K)) (v : Fin m → K) :
    (g : Matrix (Fin m) (Fin m) K) *ᵥ (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := by
  rw [mulVec_mulVec, coe_mul_coe_inv', one_mulVec]

theorem vecMul_vecMul_inv' (g : SL(m, K)) (v : Fin m → K) :
    (v ᵥ* (g : Matrix (Fin m) (Fin m) K)) ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K) = v := by
  rw [vecMul_vecMul, coe_mul_coe_inv', vecMul_one]

theorem vecMul_inv_vecMul' (g : SL(m, K)) (v : Fin m → K) :
    (v ᵥ* ((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)) ᵥ* (g : Matrix (Fin m) (Fin m) K) = v := by
  rw [vecMul_vecMul, coe_inv_mul_coe', vecMul_one]

theorem mulVec_ne_zero' (g : SL(m, K)) {v : Fin m → K} (hv : v ≠ 0) :
    (g : Matrix (Fin m) (Fin m) K) *ᵥ v ≠ 0 := fun h =>
  hv (by rw [← inv_mulVec_mulVec' g v, h, mulVec_zero])

theorem vecMul_ne_zero' (g : SL(m, K)) {v : Fin m → K} (hv : v ≠ 0) :
    v ᵥ* (g : Matrix (Fin m) (Fin m) K) ≠ 0 := fun h =>
  hv (by rw [← vecMul_vecMul_inv' g v, h, zero_vecMul])

theorem mul_comm_of_one_add {A B : Matrix (Fin m) (Fin m) K}
    (h : (1 + A) * (1 + B) = (1 + B) * (1 + A)) : A * B = B * A := by
  have e : (1 + A) * (1 + B) - (1 + B) * (1 + A) = A * B - B * A := by noncomm_ring
  rw [h, sub_self] at e
  exact (sub_eq_zero.1 e.symm)

theorem dotProduct_eq_zero_of_commute {c φ d ψ : Fin m → K} (hc : c ≠ 0) (hd : d ≠ 0)
    (hφ : φ ≠ 0) (hψ : ψ ≠ 0) (hdc : ∀ μ : K, d ≠ μ • c)
    (h : (1 + vecMulVec c φ) * (1 + vecMulVec d ψ) = (1 + vecMulVec d ψ) * (1 + vecMulVec c φ)) :
    φ ⬝ᵥ d = 0 ∧ ψ ⬝ᵥ c = 0 := by
  have hAB := mul_comm_of_one_add h
  rw [vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec] at hAB
  have h1 : φ ⬝ᵥ d = 0 := by
    by_contra hne
    obtain ⟨μ, hμ, -⟩ := exists_smul_of_vecMulVec_eq hAB hd (smul_ne_zero hne hψ)
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hc hμ
    apply hdc μ⁻¹
    rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
  refine ⟨h1, ?_⟩
  rw [h1, zero_smul, vecMulVec_zero] at hAB
  rcases vecMulVec_eq_zero.1 hAB.symm with h2 | h2
  · exact absurd h2 hd
  · exact (smul_eq_zero.1 h2).resolve_right hφ

variable [CharP K 2]

theorem add_self_eq_zero_matrix (M : Matrix (Fin m) (Fin m) K) : M + M = 0 := by
  ext i j
  simp [CharTwo.add_self_eq_zero]

theorem mul_self_sub_one_eq_zero {X : Matrix (Fin m) (Fin m) K} (h : X * X = 1) :
    (X - 1) * (X - 1) = 0 := by
  have e : X * X = 1 + ((X - 1) + (X - 1)) + (X - 1) * (X - 1) := by noncomm_ring
  rw [add_self_eq_zero_matrix, add_zero, h] at e
  have := congrArg (fun M => M - 1) e
  simpa using this.symm

theorem eq_one_of_mul_self_eq_one_char_two {μ : K} (h : μ * μ = 1) : μ = 1 := by
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact h1
  · rw [h1, CharTwo.neg_eq]

theorem det_eq_one_of_mul_self {g : Matrix (Fin m) (Fin m) K} (h : g * g = 1) : g.det = 1 := by
  apply eq_one_of_mul_self_eq_one_char_two
  rw [← det_mul, h, det_one]

end CFSG.CGT.Timmesfeld75
