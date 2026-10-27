module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalDefs

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def blockEntry (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) (j k : Fin 3) :
    Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl j) (Sum.inl k), M (Sum.inl j) (Sum.inr k);
    M (Sum.inr j) (Sum.inl k), M (Sum.inr j) (Sum.inr k)]

theorem blockEntry_mul_blockMatrix (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (m : Fin 3 → Matrix (Fin 2) (Fin 2) K) (j k : Fin 3) :
    blockEntry (M * blockMatrix m) j k = blockEntry M j k * m k := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockEntry, blockMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply,
      Fin.sum_univ_two]

theorem blockEntry_blockMatrix_mul (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)
    (m : Fin 3 → Matrix (Fin 2) (Fin 2) K) (j k : Fin 3) :
    blockEntry (blockMatrix m * M) j k = m j * blockEntry M j k := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockEntry, blockMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply,
      Fin.sum_univ_two]

theorem eq_blockMatrix_of_blockEntry_eq_zero {M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K}
    (h : ∀ j k : Fin 3, j ≠ k → blockEntry M j k = 0) :
    M = blockMatrix fun i => blockEntry M i i := by
  ext (i | i) (j | j) <;> by_cases hij : i = j
  · subst hij
    simp [blockMatrix, blockEntry]
  · have := congrFun (congrFun (h i j hij) 0) 0
    simpa [blockMatrix, blockEntry, Matrix.diagonal_apply_ne _ hij] using this
  · subst hij
    simp [blockMatrix, blockEntry]
  · have := congrFun (congrFun (h i j hij) 0) 1
    simpa [blockMatrix, blockEntry, Matrix.diagonal_apply_ne _ hij] using this
  · subst hij
    simp [blockMatrix, blockEntry]
  · have := congrFun (congrFun (h i j hij) 1) 0
    simpa [blockMatrix, blockEntry, Matrix.diagonal_apply_ne _ hij] using this
  · subst hij
    simp [blockMatrix, blockEntry]
  · have := congrFun (congrFun (h i j hij) 1) 1
    simpa [blockMatrix, blockEntry, Matrix.diagonal_apply_ne _ hij] using this

theorem exists_block_of_mem_centralizer_range_c₀ {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {g : StatedSp 3 K} (hg : g ∈ Subgroup.centralizer ((c₀ hs).range : Set (StatedSp 3 K))) :
    ∃ t : Fin 3 → SL(2, K),
      (∀ i, Commute (t i : Matrix (Fin 2) (Fin 2) K) (s : Matrix (Fin 2) (Fin 2) K)) ∧
      g = block t := by
  set M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K :=
    ((g : GL (Fin 3 ⊕ Fin 3) K) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) with hM
  have hcomm : ∀ i : Fin 3,
      M * blockMatrix (fun j => ((if j = i then s else 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) =
        blockMatrix (fun j => ((if j = i then s else 1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) *
          M := by
    intro i
    have hmem : c₀ hs (Multiplicative.ofAdd (Pi.single i 1)) ∈ (c₀ hs).range :=
      MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have h := (commute_iff_coe_commute _ _).mp ((Subgroup.mem_centralizer_iff.mp hg) _ hmem)
    rw [c₀_ofAdd_single, coe_block] at h
    exact h.symm
  have hzero : ∀ j k : Fin 3, j ≠ k → blockEntry M j k = 0 := by
    intro j k hjk
    have h := congrArg (fun A => blockEntry A j k) (hcomm k)
    simp only [blockEntry_mul_blockMatrix, blockEntry_blockMatrix_mul] at h
    simp [hjk] at h
    exact hs.eq_zero_of_mul_right_eq h
  have hM' := eq_blockMatrix_of_blockEntry_eq_zero hzero
  have hdet : ∀ i, (blockEntry M i i).det = 1 := by
    have h := mem_statedSp_iff.mp g.2
    rw [← hM] at h
    rw [hM', blockMatrix_transpose_mul_J] at h
    have h2 := (fromBlocks_inj.mp h).2.1
    intro i
    have := congrFun (congrFun h2 i) i
    simpa using this
  obtain ⟨t, ht⟩ : ∃ t : Fin 3 → SL(2, K), ∀ i, (t i : Matrix (Fin 2) (Fin 2) K) =
      blockEntry M i i := ⟨fun i => ⟨blockEntry M i i, hdet i⟩, fun i => rfl⟩
  refine ⟨t, fun i => ?_, ?_⟩
  · have h := congrArg (fun A => blockEntry A i i) (hcomm i)
    simp only [blockEntry_mul_blockMatrix, blockEntry_blockMatrix_mul] at h
    simp at h
    rw [ht]
    exact h
  · apply Subtype.ext
    apply Units.ext
    rw [coe_block, funext ht]
    exact hM'

theorem pow_eq_one_of_mem_centralizer_range_c₀ [Finite K] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {g : StatedSp 3 K} (hg : g ∈ Subgroup.centralizer ((c₀ hs).range : Set (StatedSp 3 K))) :
    g ^ (if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) = 1 := by
  obtain ⟨t, ht, rfl⟩ := exists_block_of_mem_centralizer_range_c₀ hs hg
  rw [← map_pow]
  have h : t ^ (if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) = 1 := by
    funext i
    exact hs.pow_pi_eq_one (ht i)
  rw [h, map_one]

theorem not_dvd_card_centralizer_range_c₀ [Finite K] {s : SL(2, K)} (hs : IsCubeRootBlock s)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K + 1 else Nat.card K - 1) :
    ¬ p ∣ Nat.card (Subgroup.centralizer ((c₀ hs).range : Set (StatedSp 3 K))) := by
  intro hdvd
  haveI := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hx1 : x ^ (if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_mem_centralizer_range_c₀ hs x.2
  have hpN : p ∣ if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1 :=
    hx ▸ orderOf_dvd_of_pow_eq_one hx1
  have hq : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : p ∣ 2 := by
    by_cases h3 : Nat.card K % 3 = 1
    · rw [if_pos h3] at hpq hpN
      have h := Nat.dvd_sub hpq hpN
      have e : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
      rwa [e] at h
    · rw [if_neg h3] at hpq hpN
      have h := Nat.dvd_sub hpN hpq
      have e : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
      rwa [e] at h
  have := Nat.le_of_dvd (by norm_num) h2
  omega

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
