module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockRank
public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalTensor
import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def isoMat (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![a * a, a * b, a; a * b, b * b, b; a, b, 1]

@[expose] def crossMat (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -1, b; 1, 0, -a; -b, a, 0]

theorem crossMat_mul_self {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    crossMat a b * crossMat a b = isoMat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, isoMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination (-1 : K) * h

theorem crossMat_mul_isoMat (a b : K) : crossMat a b * isoMat a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, isoMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem isoMat_mul_crossMat (a b : K) : isoMat a b * crossMat a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, isoMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem isoMat_mul_isoMat {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    isoMat a b * isoMat a b = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [isoMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination (a * a) * h | linear_combination (a * b) * h |
      linear_combination a * h | linear_combination (b * b) * h | linear_combination b * h |
      linear_combination h

theorem crossMat_transpose (a b : K) : (crossMat a b)ᵀ = -crossMat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMat]

theorem isoMat_transpose (a b : K) : (isoMat a b)ᵀ = isoMat a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [isoMat, mul_comm]

@[expose] def orthUnip (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + crossMat a b + (2 : K)⁻¹ • isoMat a b

theorem orthUnip_transpose_mul {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) (h2 : (2 : K) ≠ 0) :
    (orthUnip a b)ᵀ * orthUnip a b = 1 := by
  have hNN := crossMat_mul_self h
  have hNQ := crossMat_mul_isoMat a b
  have hQN := isoMat_mul_crossMat a b
  have hQQ := isoMat_mul_isoMat h
  have e : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  unfold orthUnip
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, crossMat_transpose,
    Matrix.transpose_smul, isoMat_transpose]
  have key : (1 + -crossMat a b + (2 : K)⁻¹ • isoMat a b) *
      (1 + crossMat a b + (2 : K)⁻¹ • isoMat a b) = 1 + (2 * (2 : K)⁻¹ - 1) • isoMat a b := by
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.one_mul, Matrix.mul_one, hNN, hNQ, hQN, hQQ, smul_zero, add_zero, smul_smul]
    module
  rw [key, show 2 * (2 : K)⁻¹ - 1 = 0 by linear_combination e, zero_smul, add_zero]

theorem orthUnip_pow {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) (h2 : (2 : K) ≠ 0) (k : ℕ) :
    (orthUnip a b) ^ k = 1 + (k : K) • crossMat a b + ((k : K) ^ 2 * 2⁻¹) • isoMat a b := by
  have hNN := crossMat_mul_self h
  have hNQ := crossMat_mul_isoMat a b
  have hQN := isoMat_mul_crossMat a b
  have hQQ := isoMat_mul_isoMat h
  have e : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    unfold orthUnip
    have hc : (((k : K) + 1) ^ 2 * 2⁻¹) = (k : K) ^ 2 * 2⁻¹ + (k : K) + 2⁻¹ := by
      linear_combination (k : K) * e
    rw [Nat.cast_succ, hc]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      hNN, hNQ, hQN, hQQ, smul_zero, add_zero, smul_smul]
    module

theorem orthUnip_pow_char {r : ℕ} [CharP K r] {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0)
    (h2 : (2 : K) ≠ 0) : (orthUnip a b) ^ r = 1 := by
  rw [orthUnip_pow h h2, CharP.cast_eq_zero]
  simp

theorem orthUnip_ne_one {a b : K} (h2 : (2 : K) ≠ 0) : orthUnip a b ≠ 1 := by
  intro h1
  have e01 := congrFun (congrFun h1 0) 1
  have e10 := congrFun (congrFun h1 1) 0
  apply h2
  simp [orthUnip, crossMat, isoMat] at e01 e10
  linear_combination e10 - e01

@[expose] noncomputable def orthUnipElement {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0)
    (h2 : (2 : K) ≠ 0) : StatedSp 3 K :=
  orthBlock (orthUnip a b) (orthUnip_transpose_mul h h2)

theorem orderOf_orthUnipElement {r : ℕ} (hr : r.Prime) [CharP K r] {a b : K}
    (h : a ^ 2 + b ^ 2 + 1 = 0) (h2 : (2 : K) ≠ 0) : orderOf (orthUnipElement h h2) = r :=
  orderOf_orthBlock hr _ _ (orthUnip_pow_char h h2) (orthUnip_ne_one h2)

@[expose] def isoNilpotent (s : SL(2, K)) (a b : K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
  tensorMatrix ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) (isoMat a b)

theorem isoNilpotent_mul_self {s : SL(2, K)} {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    isoNilpotent s a b * isoNilpotent s a b = 0 := by
  unfold isoNilpotent
  rw [tensorMatrix_mul, isoMat_mul_isoMat h, tensorMatrix_zero_right]

theorem isoNilpotent_adjoint {s : SL(2, K)} (hs : IsCubeRootBlock s) (a b : K) :
    (isoNilpotent s a b)ᵀ * fromBlocks 0 1 (-1) 0 + fromBlocks 0 1 (-1) 0 * isoNilpotent s a b =
      0 := by
  have hadj := skewPart_adjoint hs
  unfold isoNilpotent
  rw [fromBlocks_form_eq_tensorMatrix, tensorMatrix_transpose, isoMat_transpose, tensorMatrix_mul,
    tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul, ← tensorMatrix_add_left, hadj,
    tensorMatrix_zero_left]

theorem isoNilpotent_ne_zero {s : SL(2, K)} (hs : IsCubeRootBlock s) (a b : K) :
    isoNilpotent s a b ≠ 0 := by
  intro h0
  have hP : ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [isoNilpotent, tensorMatrix, isoMat] using
        congrFun (congrFun h0 (Sum.inl 2)) (Sum.inl 2)
    · simpa [isoNilpotent, tensorMatrix, isoMat] using
        congrFun (congrFun h0 (Sum.inl 2)) (Sum.inr 2)
    · simpa [isoNilpotent, tensorMatrix, isoMat] using
        congrFun (congrFun h0 (Sum.inr 2)) (Sum.inl 2)
    · simpa [isoNilpotent, tensorMatrix, isoMat] using
        congrFun (congrFun h0 (Sum.inr 2)) (Sum.inr 2)
  have := hs.two_smul_add_one_sq
  rw [sq, hP, Matrix.zero_mul] at this
  have h00 := congrFun (congrFun this 0) 0
  simp at h00
  exact hs.three_ne_zero h00

@[expose] noncomputable def isoElement {s : SL(2, K)} (hs : IsCubeRootBlock s) {a b : K}
    (h : a ^ 2 + b ^ 2 + 1 = 0) : StatedSp 3 K :=
  unipotentSp (isoNilpotent s a b) (isoNilpotent_adjoint hs a b) (isoNilpotent_mul_self h)

theorem orderOf_isoElement {r : ℕ} (hr : r.Prime) [CharP K r] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    orderOf (isoElement hs h) = r :=
  orderOf_unipotentSp hr _ _ _ (isoNilpotent_ne_zero hs a b)

theorem commute_c₀_point_111_isoElement {s : SL(2, K)} (hs : IsCubeRootBlock s) {a b : K}
    (h : a ^ 2 + b ^ 2 + 1 = 0) :
    Commute (c₀ hs (Multiplicative.ofAdd ![1, 1, 1])) (isoElement hs h) := by
  rw [commute_iff_coe_commute, c₀_point_111, coe_block_vec, blockMatrix_vec_const]
  have hsP : Commute (s : Matrix (Fin 2) (Fin 2) K)
      ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) :=
    ((Commute.refl _).smul_right 2).add_right (Commute.one_right _)
  refine (Commute.one_right _).add_right ?_
  unfold Commute SemiconjBy isoNilpotent
  rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul, hsP.eq]

theorem isoMat_mul_orthUnip {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    isoMat a b * orthUnip a b = isoMat a b := by
  unfold orthUnip
  simp only [mul_add, Matrix.mul_one, Matrix.mul_smul, isoMat_mul_crossMat, isoMat_mul_isoMat h,
    smul_zero, add_zero]

theorem orthUnip_mul_isoMat {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) :
    orthUnip a b * isoMat a b = isoMat a b := by
  unfold orthUnip
  simp only [add_mul, Matrix.one_mul, Matrix.smul_mul, crossMat_mul_isoMat, isoMat_mul_isoMat h,
    smul_zero, add_zero]

theorem commute_isoElement_orthUnipElement {s : SL(2, K)} (hs : IsCubeRootBlock s) {a b : K}
    (h : a ^ 2 + b ^ 2 + 1 = 0) (h2 : (2 : K) ≠ 0) :
    Commute (isoElement hs h) (orthUnipElement h h2) := by
  rw [commute_iff_coe_commute]
  change Commute (1 + isoNilpotent s a b) (tensorMatrix 1 (orthUnip a b))
  refine (Commute.one_left _).add_left ?_
  unfold Commute SemiconjBy isoNilpotent
  rw [tensorMatrix_mul, tensorMatrix_mul, Matrix.mul_one, Matrix.one_mul, isoMat_mul_orthUnip h,
    orthUnip_mul_isoMat h]

theorem orthUnipElement_not_mem_zpowers_isoElement {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {a b : K} (h : a ^ 2 + b ^ 2 + 1 = 0) (h2 : (2 : K) ≠ 0) :
    orthUnipElement h h2 ∉ Subgroup.zpowers (isoElement hs h) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hm := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hk
  simp only [isoElement, orthUnipElement, coe_unipotentSp_zpow, coe_orthBlock] at hm
  have e01 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 1)
  have e10 := congrFun (congrFun hm (Sum.inl 1)) (Sum.inl 0)
  apply h2
  simp [isoNilpotent, tensorMatrix, orthUnip, crossMat, isoMat] at e01 e10
  linear_combination e01 - e10

theorem two_le_pRank_centralizer_c₀_weight_three [Finite K] {r : ℕ} (hr : r.Prime) [CharP K r]
    (h5 : 5 ≤ r) {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    2 ≤ CFSG.Open.pRank r (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K))) := by
  haveI := Fact.mk hr
  obtain ⟨a, b, h⟩ := exists_sq_add_sq_eq_neg_one (K := K) hr
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_five_le h5
  have hu₁ : isoElement hs h ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_point_111_isoElement hs h).symm.eq
  have hu₂ : orthUnipElement h h2 ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_point_111_orthBlock hs _ _).symm.eq
  exact CFSG.GroupTheory.two_le_pRank_of_commute hu₁ hu₂ (orderOf_isoElement hr hs h)
    (orderOf_orthUnipElement hr h h2) (commute_isoElement_orthUnipElement hs h h2)
    (orthUnipElement_not_mem_zpowers_isoElement hs h h2)

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
