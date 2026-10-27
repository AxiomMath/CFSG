module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalTensor

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

structure IsHyperbolicPair (n n' : Fin 3 → K) : Prop where
  dot_self_left : n ⬝ᵥ n = 0
  dot_self_right : n' ⬝ᵥ n' = 0
  dot_ne_zero : n ⬝ᵥ n' ≠ 0

@[expose] def hypProj₁ (n n' : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (n ⬝ᵥ n')⁻¹ • vecMulVec n n'

@[expose] def hypProj₂ (n n' : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  (n ⬝ᵥ n')⁻¹ • vecMulVec n' n

namespace IsHyperbolicPair

variable {n n' : Fin 3 → K}

theorem proj₁_mul_proj₁ (h : IsHyperbolicPair n n') :
    hypProj₁ n n' * hypProj₁ n n' = hypProj₁ n n' := by
  unfold hypProj₁
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, dotProduct_comm n' n]
  simp only [Matrix.vecMulVec_smul, smul_smul]
  congr 1
  rw [inv_mul_cancel₀ h.dot_ne_zero, mul_one]

theorem proj₁_mul_proj₂ (h : IsHyperbolicPair n n') :
    hypProj₁ n n' * hypProj₂ n n' = 0 := by
  unfold hypProj₁ hypProj₂
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, h.dot_self_right]
  simp

theorem proj₂_mul_proj₁ (h : IsHyperbolicPair n n') :
    hypProj₂ n n' * hypProj₁ n n' = 0 := by
  unfold hypProj₁ hypProj₂
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, h.dot_self_left]
  simp

theorem proj₂_mul_proj₂ (h : IsHyperbolicPair n n') :
    hypProj₂ n n' * hypProj₂ n n' = hypProj₂ n n' := by
  unfold hypProj₂
  rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  simp only [Matrix.vecMulVec_smul, smul_smul]
  congr 1
  rw [inv_mul_cancel₀ h.dot_ne_zero, mul_one]

theorem proj₁_transpose : (hypProj₁ n n')ᵀ = hypProj₂ n n' := by
  unfold hypProj₁ hypProj₂
  rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec, dotProduct_comm]

theorem proj₂_transpose : (hypProj₂ n n')ᵀ = hypProj₁ n n' := by
  unfold hypProj₁ hypProj₂
  rw [Matrix.transpose_smul, Matrix.transpose_vecMulVec, dotProduct_comm]

end IsHyperbolicPair

@[expose] def orthTorus (n n' : Fin 3 → K) (l : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + (l - 1) • hypProj₁ n n' + (l⁻¹ - 1) • hypProj₂ n n'

theorem orthTorus_one (n n' : Fin 3 → K) : orthTorus n n' 1 = 1 := by
  simp [orthTorus]

theorem orthTorus_mul {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') (x y : K) :
    orthTorus n n' x * orthTorus n n' y = orthTorus n n' (x * y) := by
  unfold orthTorus
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    h.proj₁_mul_proj₁, h.proj₁_mul_proj₂, h.proj₂_mul_proj₁, h.proj₂_mul_proj₂, smul_zero,
    add_zero, smul_smul, mul_inv]
  module

theorem orthTorus_transpose {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') (l : K) :
    (orthTorus n n' l)ᵀ = orthTorus n n' l⁻¹ := by
  unfold orthTorus
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    Matrix.transpose_smul, IsHyperbolicPair.proj₁_transpose, IsHyperbolicPair.proj₂_transpose,
    inv_inv]
  abel

theorem orthTorus_transpose_mul {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') {l : K}
    (hl : l ≠ 0) : (orthTorus n n' l)ᵀ * orthTorus n n' l = 1 := by
  rw [orthTorus_transpose h, orthTorus_mul h, inv_mul_cancel₀ hl, orthTorus_one]

theorem orthTorus_pow {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') (l : K) (k : ℕ) :
    (orthTorus n n' l) ^ k = orthTorus n n' (l ^ k) := by
  induction k with
  | zero => simp [orthTorus_one]
  | succ k ih => rw [pow_succ, ih, orthTorus_mul h, pow_succ]

theorem orthTorus_mulVec {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') (l : K) :
    orthTorus n n' l *ᵥ n = l • n := by
  have hc := h.dot_ne_zero
  have h1 : hypProj₁ n n' *ᵥ n = n := by
    unfold hypProj₁
    rw [Matrix.smul_mulVec, vecMulVec_mulVec, dotProduct_comm n' n]
    simp [hc]
  have h2 : hypProj₂ n n' *ᵥ n = 0 := by
    unfold hypProj₂
    rw [Matrix.smul_mulVec, vecMulVec_mulVec, h.dot_self_left]
    simp
  unfold orthTorus
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, h1, h2,
    Matrix.one_mulVec]
  simp only [smul_zero, add_zero, sub_smul, one_smul]
  abel

theorem orthTorus_ne_one {n n' : Fin 3 → K} (h : IsHyperbolicPair n n') {l : K} (hl : l ≠ 1) :
    orthTorus n n' l ≠ 1 := by
  intro h1
  have hv := orthTorus_mulVec h l
  rw [h1, Matrix.one_mulVec] at hv
  have hn : n ≠ 0 := fun h0 => h.dot_ne_zero (by simp [h0])
  apply hn
  funext i
  have h3 := congrFun hv i
  simp only [Pi.smul_apply, smul_eq_mul] at h3
  have h4 : (l - 1) * n i = 0 := by linear_combination -h3
  rcases mul_eq_zero.mp h4 with h' | h'
  · exact absurd (sub_eq_zero.mp h') hl
  · exact h'

@[expose] noncomputable def orthTorusElement {n n' : Fin 3 → K} (h : IsHyperbolicPair n n')
    {l : K} (hl : l ≠ 0) : StatedSp 3 K :=
  orthBlock (orthTorus n n' l) (orthTorus_transpose_mul h hl)

theorem orderOf_orthTorusElement {n n' : Fin 3 → K} {p : ℕ} (hp : p.Prime)
    (h : IsHyperbolicPair n n') {l : K} (hl : l ≠ 0) (hlp : l ^ p = 1) (hl1 : l ≠ 1) :
    orderOf (orthTorusElement h hl) = p :=
  orderOf_orthBlock hp _ _ (by rw [orthTorus_pow h, hlp, orthTorus_one]) (orthTorus_ne_one h hl1)

theorem exists_hyperbolicPair [Finite K] : ∃ n n' : Fin 3 → K, IsHyperbolicPair n n' := by
  by_cases h2 : (2 : K) = 0
  · refine ⟨![1, 1, 0], ![0, 1, 1], ⟨?_, ?_, ?_⟩⟩
    · simp [dotProduct, Fin.sum_univ_three]
      linear_combination h2
    · simp [dotProduct, Fin.sum_univ_three]
      linear_combination h2
    · simp [dotProduct, Fin.sum_univ_three]
  · obtain ⟨a, b, hab⟩ := exists_isotropic (K := K)
    refine ⟨![a, b, 1], ![-a, -b, 1], ⟨?_, ?_, ?_⟩⟩
    · simp [dotProduct, Fin.sum_univ_three]
      linear_combination hab
    · simp [dotProduct, Fin.sum_univ_three]
      linear_combination hab
    · simp [dotProduct, Fin.sum_univ_three]
      intro h0
      apply h2
      linear_combination h0 + hab

theorem dvd_card_centralizer_c₀_weight_three_of_dvd_sub_one [Finite K] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K))) := by
  haveI := Fact.mk hp
  obtain ⟨n, n', h⟩ := exists_hyperbolicPair (K := K)
  have hcard : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hlp : (u : K) ^ p = 1 := by
    have : u ^ p = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    simpa using congrArg (fun v : Kˣ => (v : K)) this
  have hl1 : (u : K) ≠ 1 := by
    intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    exact hp.one_lt.ne hu
  have hmem : orthTorusElement h u.ne_zero ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_point_111_orthBlock hs _ _).symm.eq
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [orderOf_orthTorusElement hp h u.ne_zero hlp hl1] at this

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
