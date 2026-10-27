module

public import CFSG.LieType.SemisimpleCentralizers.HeldSLFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held Matrix

variable {K : Type} [Field K]

theorem single_mul_single_self_eq_zero {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    (Matrix.single i j (1 : K)) * Matrix.single i j (1 : K) = 0 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases h1 : i = x ∧ j = l <;> by_cases h2 : i = k ∧ j = x <;> simp_all

theorem isScalar_of_commute_single {d : ℕ} (M : Matrix (Fin d) (Fin d) K)
    (hcomm : ∀ i j : Fin d, i ≠ j → M * Matrix.single i j (1 : K) = Matrix.single i j (1 : K) * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin d) (Fin d) K) := by
  have hoff : ∀ x y : Fin d, x ≠ y → M x y = 0 := by
    intro x y hxy
    have h := congrFun (congrFun (hcomm y x (Ne.symm hxy)) x) x
    simp [Matrix.mul_apply, Matrix.single_apply, hxy, Ne.symm hxy] at h
    exact h
  have hdiag : ∀ i j : Fin d, i ≠ j → M i i = M j j := by
    intro i j hij
    have h := congrFun (congrFun (hcomm i j hij) i) j
    simpa [Matrix.mul_apply, Matrix.single_apply] using h
  by_cases hd : (Nonempty (Fin d))
  · obtain ⟨i0⟩ := hd
    refine ⟨M i0 i0, ?_⟩
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x = i0
      · subst hx; simp
      · simp [Matrix.smul_apply, Matrix.one_apply, hx]
        exact hdiag x i0 hx
    · simp [Matrix.smul_apply, Matrix.one_apply, hxy, hoff x y hxy]
  · refine ⟨0, ?_⟩
    ext x; exact (hd ⟨x⟩).elim

theorem commute_single_of_conj_scalar {d : ℕ} (h2 : (2 : K) = 0) (B : GL (Fin d) K) {i j : Fin d}
    (hij : i ≠ j) (c : K)
    (hc : (B : Matrix (Fin d) (Fin d) K) * (1 + Matrix.single i j (1 : K)) =
      c • (1 + Matrix.single i j (1 : K)) * (B : Matrix (Fin d) (Fin d) K)) :
    (B : Matrix (Fin d) (Fin d) K) * Matrix.single i j (1 : K) =
      Matrix.single i j (1 : K) * (B : Matrix (Fin d) (Fin d) K) := by
  set Bm : Matrix (Fin d) (Fin d) K := (B : Matrix (Fin d) (Fin d) K) with hBm
  set Bi : Matrix (Fin d) (Fin d) K := ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hBi
  set N : Matrix (Fin d) (Fin d) K := Matrix.single i j (1 : K) with hNdef
  have hN : N * N = 0 := single_mul_single_self_eq_zero hij
  have hBBi : Bm * Bi = 1 := Units.mul_inv B
  have hBiB : Bi * Bm = 1 := Units.inv_mul B
  have E1 : Bm * N = (c - 1) • Bm + c • (N * Bm) := by
    have h' : Bm + Bm * N = c • Bm + c • (N * Bm) := by
      have := hc
      simp only [mul_add, mul_one, add_mul, one_mul, smul_add, smul_mul_assoc] at this
      exact this
    calc Bm * N = (Bm + Bm * N) - Bm := by abel
      _ = (c • Bm + c • (N * Bm)) - Bm := by rw [h']
      _ = (c - 1) • Bm + c • (N * Bm) := by rw [sub_smul, one_smul]; abel
  have hPN : (N * Bm) * N = (c - 1) • (N * Bm) := by
    calc (N * Bm) * N = N * (Bm * N) := by rw [mul_assoc]
      _ = N * ((c - 1) • Bm + c • (N * Bm)) := by rw [E1]
      _ = (c - 1) • (N * Bm) + c • ((N * N) * Bm) := by
            rw [mul_add, mul_smul_comm, mul_smul_comm, ← mul_assoc]
      _ = (c - 1) • (N * Bm) := by rw [hN]; simp
  have F : (c - 1) ^ 2 • Bm = 0 := by
    have h0 : Bm * N * N = 0 := by rw [mul_assoc, hN, mul_zero]
    rw [E1, add_mul, smul_mul_assoc, smul_mul_assoc, hPN] at h0
    rw [E1] at h0
    simp only [smul_add, smul_smul] at h0
    have hz : (c - 1) * c + c * (c - 1) = 0 := by linear_combination (c ^ 2 - c) * h2
    have hsum : ((c - 1) * c) • (N * Bm) + (c * (c - 1)) • (N * Bm) = 0 := by
      rw [← add_smul, hz, zero_smul]
    have h0' : ((c - 1) * (c - 1)) • Bm + (((c - 1) * c) • (N * Bm) + (c * (c - 1)) • (N * Bm)) = 0 := by
      rw [← add_assoc]; exact h0
    rw [hsum, add_zero] at h0'
    rw [sq]; exact h0'
  have F1 : (c - 1) ^ 2 • (1 : Matrix (Fin d) (Fin d) K) = 0 := by
    have := congrArg (fun X => X * Bi) F
    simpa [smul_mul_assoc, hBBi] using this
  have hc1 : (c - 1) ^ 2 = 0 := by
    have := congrFun (congrFun F1 i) i
    simpa using this
  have hc0 : c = 1 := by
    have : c - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hc1
    exact sub_eq_zero.mp this
  rw [E1, hc0]
  simp

theorem gl_isScalar_of_conj_mod_scalar {d : ℕ} (h2 : (2 : K) = 0) (B : GL (Fin d) K)
    (H : ∀ g : GL (Fin d) K, g ∈ CFSG.Open.StatedSL d K → ∃ c : K,
      (B : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
        ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K)) :
    ∃ c : K, (B : Matrix (Fin d) (Fin d) K) = c • (1 : Matrix (Fin d) (Fin d) K) := by
  have hBiB : ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) = 1 :=
    Units.inv_mul B
  have hcomm : ∀ i j : Fin d, i ≠ j →
      (B : Matrix (Fin d) (Fin d) K) * Matrix.single i j (1 : K) =
        Matrix.single i j (1 : K) * (B : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    obtain ⟨c, hc⟩ := H (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1))
      (transvection_toGL_mem_statedSL hij 1)
    have ht : ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1) :
        GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + Matrix.single i j (1 : K) := rfl
    rw [ht] at hc
    have hc' : (B : Matrix (Fin d) (Fin d) K) * (1 + Matrix.single i j (1 : K)) =
        c • (1 + Matrix.single i j (1 : K)) * (B : Matrix (Fin d) (Fin d) K) := by
      have h3 : (B : Matrix (Fin d) (Fin d) K) * (1 + Matrix.single i j (1 : K)) =
          (B : Matrix (Fin d) (Fin d) K) * (1 + Matrix.single i j (1 : K)) *
            ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) := by
        rw [mul_assoc, hBiB, mul_one]
      rw [h3, hc]
    exact commute_single_of_conj_scalar h2 B hij c hc'
  exact isScalar_of_commute_single (B : Matrix (Fin d) (Fin d) K) hcomm

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin

end
