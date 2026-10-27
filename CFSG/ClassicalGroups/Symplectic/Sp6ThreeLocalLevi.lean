module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalTensor
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_orderOf_eq_specialLinearGroup [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K ^ 2 - 1) : ∃ z : SL(2, K), orderOf z = p := by
  haveI := Fact.mk hp
  have : p ∣ Nat.card SL(2, K) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    exact Dvd.dvd.mul_left hpq _
  exact exists_prime_orderOf_dvd_card' p this

@[expose] def leviMat (z : SL(2, K)) : Matrix (Fin 3) (Fin 3) K :=
  !![(z : Matrix (Fin 2) (Fin 2) K) 0 0, (z : Matrix (Fin 2) (Fin 2) K) 0 1, 0;
    (z : Matrix (Fin 2) (Fin 2) K) 1 0, (z : Matrix (Fin 2) (Fin 2) K) 1 1, 0; 0, 0, 1]

theorem leviMat_mul (z w : SL(2, K)) : leviMat (z * w) = leviMat z * leviMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leviMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem leviMat_one : leviMat (1 : SL(2, K)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [leviMat]

@[expose] noncomputable def leviSp (M N : Matrix (Fin 3) (Fin 3) K) (h₁ : M * N = 1)
    (h₂ : N * M = 1) : StatedSp 3 K :=
  mkSp (fromBlocks M 0 0 Nᵀ) (fromBlocks N 0 0 Mᵀ)
    (by
      rw [fromBlocks_multiply]
      simp [h₁, ← Matrix.transpose_mul, h₂])
    (by
      rw [fromBlocks_multiply]
      simp [h₂, ← Matrix.transpose_mul, h₁])
    (by
      rw [fromBlocks_transpose]
      simp only [Matrix.transpose_zero, Matrix.transpose_transpose]
      rw [fromBlocks_multiply, fromBlocks_multiply]
      simp [← Matrix.transpose_mul, h₂])

theorem coe_leviSp (M N : Matrix (Fin 3) (Fin 3) K) (h₁ : M * N = 1) (h₂ : N * M = 1) :
    (((leviSp M N h₁ h₂ : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = fromBlocks M 0 0 Nᵀ :=
  rfl

@[expose] noncomputable def leviSL : SL(2, K) →* StatedSp 3 K where
  toFun z := leviSp (leviMat z) (leviMat z⁻¹)
    (by rw [← leviMat_mul, mul_inv_cancel, leviMat_one])
    (by rw [← leviMat_mul, inv_mul_cancel, leviMat_one])
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change fromBlocks (leviMat (1 : SL(2, K))) 0 0 (leviMat (1 : SL(2, K))⁻¹)ᵀ = 1
    simp [leviMat_one, fromBlocks_one]
  map_mul' z w := by
    apply Subtype.ext
    apply Units.ext
    change fromBlocks (leviMat (z * w)) 0 0 (leviMat (z * w)⁻¹)ᵀ =
      fromBlocks (leviMat z) 0 0 (leviMat z⁻¹)ᵀ * fromBlocks (leviMat w) 0 0 (leviMat w⁻¹)ᵀ
    rw [fromBlocks_multiply, leviMat_mul, _root_.mul_inv_rev, leviMat_mul, Matrix.transpose_mul]
    simp

theorem coe_leviSL (z : SL(2, K)) :
    (((leviSL z : StatedSp 3 K) : GL (Fin 3 ⊕ Fin 3) K) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) = fromBlocks (leviMat z) 0 0 (leviMat z⁻¹)ᵀ :=
  rfl

theorem leviSL_injective : Function.Injective (leviSL : SL(2, K) →* StatedSp 3 K) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have h := congrArg (fun g : StatedSp 3 K => (((g : GL (Fin 3 ⊕ Fin 3) K) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K))) hz
  simp only [coe_leviSL] at h
  have h00 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 0)
  have h01 := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
  have h10 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 0)
  have h11 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
  simp [leviMat] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

theorem orderOf_leviSL (z : SL(2, K)) : orderOf (leviSL z) = orderOf z :=
  orderOf_injective _ leviSL_injective z

theorem commute_c₀_point_111_leviSL {s : SL(2, K)} (hs : IsCubeRootBlock s) {ω : Kˣ}
    (hsω : s = cubeRootDiag ω) (z : SL(2, K)) :
    Commute (c₀ hs (Multiplicative.ofAdd ![1, 1, 1])) (leviSL z) := by
  rw [commute_iff_coe_commute, c₀_point_111, coe_block_vec, blockMatrix_vec_const, coe_leviSL,
    hsω]
  have e : tensorMatrix ((cubeRootDiag ω : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 =
      fromBlocks ((ω : K) • (1 : Matrix (Fin 3) (Fin 3) K)) 0 0
        (((ω⁻¹ : Kˣ) : K) • (1 : Matrix (Fin 3) (Fin 3) K)) := by
    simp [tensorMatrix, cubeRootDiag]
  rw [e]
  unfold Commute SemiconjBy
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.smul_mul, Matrix.mul_smul]

theorem dvd_card_centralizer_c₀_weight_three_of_dvd_add_one [Finite K] {s : SL(2, K)}
    (hs : IsCubeRootBlock s) {ω : Kˣ} (hsω : s = cubeRootDiag ω) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ Nat.card K + 1) :
    p ∣ Nat.card (Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K))) := by
  have hsq : p ∣ Nat.card K ^ 2 - 1 := by
    have h : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.card K) with h0 | hq
      · simp [h0]
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
        rw [hn]
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        apply Nat.sub_eq_of_eq_add
        ring
    rw [h]
    exact Dvd.dvd.mul_right hpq _
  obtain ⟨z, hz⟩ := exists_orderOf_eq_specialLinearGroup (K := K) hp hsq
  have hmem : leviSL z ∈ Subgroup.centralizer
      ({c₀ hs (Multiplicative.ofAdd ![1, 1, 1])} : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_c₀_point_111_leviSL hs hsω z).symm.eq
  have := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [orderOf_leviSL, hz] at this

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
