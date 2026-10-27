module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA6LSL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

open Matrix

variable {K : Type} [Field K]

theorem offblock_of_commute_proj (M : Matrix (Fin 6) (Fin 6) K)
    (h : M * blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) =
      blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) * M) :
    (∀ a b, M (ia a) (ib b) = 0) ∧ (∀ a b, M (ib a) (ia b) = 0) := by
  constructor
  · intro a b
    have h1 := congrFun (congrFun h (ia a)) (ib b)
    simp only [Matrix.mul_apply, sum6_blocks, blk6_ia_ia, blk6_ia_ib, blk6_ib_ia, blk6_ib_ib,
      Matrix.one_apply, Matrix.zero_apply, ia_inj', ib_inj', mul_zero, zero_mul, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, zero_add, add_zero,
      ite_mul, mul_ite, one_mul] at h1
    exact h1.symm
  · intro a b
    have h1 := congrFun (congrFun h (ib a)) (ia b)
    simp only [Matrix.mul_apply, sum6_blocks, blk6_ia_ia, blk6_ia_ib, blk6_ib_ia, blk6_ib_ib,
      Matrix.one_apply, Matrix.zero_apply, ia_inj', ib_inj', mul_zero, zero_mul, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, zero_add, add_zero,
      ite_mul, mul_ite, one_mul] at h1
    exact h1

theorem blk6_snd_inj {M M' : Matrix (Fin 4) (Fin 4) K} {N N' : Matrix (Fin 2) (Fin 2) K}
    (h : blk6 M N = blk6 M' N') : N = N' := by
  ext a b
  have := congrFun (congrFun h (ib a)) (ib b)
  rwa [blk6_ib_ib, blk6_ib_ib] at this

theorem blk6_comm_iff (A D : Matrix (Fin 4) (Fin 4) K) (B T : Matrix (Fin 2) (Fin 2) K) :
    blk6 A B * blk6 D T = blk6 D T * blk6 A B ↔ A * D = D * A ∧ B * T = T * B := by
  rw [← blk6_mul, ← blk6_mul]
  constructor
  · intro h
    exact ⟨blk6_fst_inj h, blk6_snd_inj h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

open Classical in
theorem normal_Psi (C C' : Matrix (Fin 6) (Fin 6) K) (T2 : Matrix (Fin 2) (Fin 2) K)
    (hCC' : C * C' = 1) (hC'C : C' * C = 1)
    (ha : C * blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) =
      blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) * C)
    (hb : C * blk6 (D4 K) T2 = blk6 (D4 K) T2 * C)
    (ha' : C' * blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) =
      blk6 (1 : Matrix (Fin 4) (Fin 4) K) (0 : Matrix (Fin 2) (Fin 2) K) * C')
    (hb' : C' * blk6 (D4 K) T2 = blk6 (D4 K) T2 * C')
    (X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K))) [Fact (Irreducible (KA7.quad K))]
    [Finite (AdjoinRoot (KA7.quad K))] :
    ∃ Y Y' : Matrix (Fin 2) (Fin 2) (AdjoinRoot (KA7.quad K)), Y * Y' = 1 ∧ Y' * Y = 1 ∧
      C * blk6 (Theta X) 1 * C' = blk6 (Theta (Y * X * Y')) 1 := by
  obtain ⟨C1, hC1⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K, M = Matrix.of fun a b => C (ia a) (ia b) :=
    ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = Matrix.of fun a b => C (ib a) (ib b) :=
    ⟨_, rfl⟩
  obtain ⟨C1', hC1'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K, M = Matrix.of fun a b => C' (ia a) (ia b) :=
    ⟨_, rfl⟩
  obtain ⟨C2', hC2'⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = Matrix.of fun a b => C' (ib a) (ib b) :=
    ⟨_, rfl⟩
  have hCblk : C = blk6 C1 C2 := by
    rw [hC1, hC2]
    exact eq_blk6_of_offblock C (offblock_of_commute_proj C ha).1 (offblock_of_commute_proj C ha).2
  have hC'blk : C' = blk6 C1' C2' := by
    rw [hC1', hC2']
    exact eq_blk6_of_offblock C' (offblock_of_commute_proj C' ha').1
      (offblock_of_commute_proj C' ha').2
  have hC1D : C1 * D4 K = D4 K * C1 := by
    rw [hCblk] at hb
    exact ((blk6_comm_iff C1 (D4 K) C2 T2).mp hb).1
  have hC1D' : C1' * D4 K = D4 K * C1' := by
    rw [hC'blk] at hb'
    exact ((blk6_comm_iff C1' (D4 K) C2' T2).mp hb').1
  obtain ⟨Y, hY⟩ := commutant_Theta K C1 hC1D
  obtain ⟨Y', hY'⟩ := commutant_Theta K C1' hC1D'
  have hprod : blk6 (C1 * C1') (C2 * C2') = blk6 1 1 := by
    rw [blk6_one, blk6_mul, ← hCblk, ← hC'blk, hCC']
  have hprod' : blk6 (C1' * C1) (C2' * C2) = blk6 1 1 := by
    rw [blk6_one, blk6_mul, ← hC'blk, ← hCblk, hC'C]
  have hC1C1' : C1 * C1' = 1 := blk6_fst_inj (by rw [hprod, blk6_one])
  have hC1'C1 : C1' * C1 = 1 := blk6_fst_inj (by rw [hprod', blk6_one])
  have hC2C2' : C2 * C2' = 1 := blk6_snd_inj (by rw [hprod, blk6_one])
  have hC2'C2 : C2' * C2 = 1 := blk6_snd_inj (by rw [hprod', blk6_one])
  refine ⟨Y, Y', ?_, ?_, ?_⟩
  · apply Theta_injective K
    rw [Theta_mul, hY, hY', hC1C1', Theta_one]
  · apply Theta_injective K
    rw [Theta_mul, hY, hY', hC1'C1, Theta_one]
  · have h := congrArg id (show C * blk6 (Theta X) 1 * C' = blk6 (Theta Y * Theta X * Theta Y') (C2 * 1 * C2') by
      rw [hCblk, hC'blk, ← hY, ← hY', blk6_mul, blk6_mul])
    rw [mul_one, hC2C2', ← Theta_mul, ← Theta_mul] at h
    exact h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA6L

end
