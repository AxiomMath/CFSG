module

public import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GUEigen

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem sigma_omega (hσ : IsUnitaryInvolution σ) {ω : K} (hω : IsPrimitiveRoot ω 3)
    (hF3 : ∀ ν : K, σ ν = ν → ν ^ 3 = 1 → ν = 1) : σ ω * ω = 1 := by
  have h3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hν : σ (ω * σ ω) = ω * σ ω := by
    rw [map_mul, hσ.invol, mul_comm]
  have := hF3 (ω * σ ω) hν (by
    rw [mul_pow, ← map_pow, h3, map_one, mul_one])
  rw [mul_comm, this]

theorem herm_eq_zero_of_eigen {y : Matrix (Fin n) (Fin n) K} (hy : conjTr σ y * y = 1)
    {u u' : Fin n → K} {l l' : K} (hu : y *ᵥ u = l • u) (hu' : y *ᵥ u' = l' • u')
    (hne : σ l * l' ≠ 1) : herm σ u u' = 0 := by
  have h1 := herm_mulVec_isometry hy u u'
  rw [hu, hu', herm_smul_left, herm_smul_right, ← mul_assoc] at h1
  by_contra h
  exact hne (mul_right_cancel₀ h (h1.trans (one_mul _).symm))

theorem mul_of_cols (T : Matrix (Fin n) (Fin n) K) (s : Fin n → Fin n → K) (D : Fin n → K)
    (h : ∀ j, T *ᵥ s j = D j • s j) :
    T * (Matrix.of fun i j => s j i) = (Matrix.of fun i j => s j i) * Matrix.diagonal D := by
  ext i j
  have := congrFun (h j) i
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem conjTr_mul_of_orthonormal (s : Fin n → Fin n → K)
    (hs : ∀ i j, herm σ (s i) (s j) = if i = j then 1 else 0) :
    conjTr σ (Matrix.of fun i j => s j i) * (Matrix.of fun i j => s j i) = 1 := by
  ext i j
  have := hs i j
  rw [herm_def] at this
  simp only [conjTr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
    this]
  rw [Matrix.one_apply]

theorem scalar_mulVec' (a : K) (x : Fin n → K) : (Matrix.scalar (Fin n) a) *ᵥ x = a • x := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem mulVec_injective_of_isometry {A : Matrix (Fin n) (Fin n) K} (hA : conjTr σ A * A = 1)
    {x : Fin n → K} (hx : A *ᵥ x = 0) : x = 0 := by
  have : x = (conjTr σ A * A) *ᵥ x := by rw [hA, one_mulVec]
  rw [this, ← mulVec_mulVec, hx, mulVec_zero]

theorem exists_unitary_normal_form (hσ : IsUnitaryInvolution σ)
    (hF3 : ∀ ν : K, σ ν = ν → ν ^ 3 = 1 → ν = 1) {ω : K} (hω : IsPrimitiveRoot ω 3)
    {y w : Matrix (Fin 3) (Fin 3) K} (hy : conjTr σ y * y = 1) (hw : conjTr σ w * w = 1)
    (hyw : y * w = Matrix.scalar (Fin 3) ω * (w * y)) {b : K}
    (hw3 : w ^ 3 = Matrix.scalar (Fin 3) b) {v : Fin 3 → K} (hv : v ≠ 0) (hyv : y *ᵥ v = v) :
    ∃ M : Matrix (Fin 3) (Fin 3) K, conjTr σ M * M = 1 ∧
      y * M = M * Matrix.diagonal ![1, ω, ω ^ 2] ∧
      w * M = M * !![0, 0, b; 1, 0, 0; 0, 1, 0] := by
  have hσω := sigma_omega hσ hω hF3
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : ω ^ 2 ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hyw' : ∀ x, y *ᵥ (w *ᵥ x) = ω • (w *ᵥ (y *ᵥ x)) := by
    intro x
    rw [mulVec_mulVec, hyw, ← mulVec_mulVec, scalar_mulVec', mulVec_mulVec]
  have hw3v : ∀ x, w *ᵥ (w *ᵥ (w *ᵥ x)) = b • x := by
    intro x
    rw [mulVec_mulVec, mulVec_mulVec, show w * w * w = w ^ 3 by rw [pow_succ, pow_two], hw3,
      scalar_mulVec']
  set u0 : Fin 3 → K := v with hu0
  set u1 : Fin 3 → K := w *ᵥ v with hu1
  set u2 : Fin 3 → K := w *ᵥ u1 with hu2
  have e0 : y *ᵥ u0 = (1 : K) • u0 := by rw [one_smul]; exact hyv
  have e1 : y *ᵥ u1 = ω • u1 := by
    rw [hu1, hyw', hyv]
  have e2 : y *ᵥ u2 = (ω ^ 2) • u2 := by
    rw [hu2, hyw', e1, mulVec_smul, smul_smul, pow_two]
  have hw0 : u1 ≠ 0 := fun h => hv (mulVec_injective_of_isometry hw h)
  have hw1 : u2 ≠ 0 := fun h => hw0 (mulVec_injective_of_isometry hw h)
  have o01 : herm σ u0 u1 = 0 := herm_eq_zero_of_eigen (l := (1 : K)) (l' := ω) hy e0 e1 (by rw [map_one, one_mul]; exact hω1)
  have o02 : herm σ u0 u2 = 0 :=
    herm_eq_zero_of_eigen (l := (1 : K)) (l' := ω ^ 2) hy e0 e2 (by rw [map_one, one_mul]; exact hω2)
  have o12 : herm σ u1 u2 = 0 := herm_eq_zero_of_eigen (l := ω) (l' := ω ^ 2) hy e1 e2 (by
    rw [pow_two, ← mul_assoc, hσω, one_mul]; exact hω1)
  have o10 := herm_eq_zero_comm σ hσ.invol o01
  have o20 := herm_eq_zero_comm σ hσ.invol o02
  have o21 := herm_eq_zero_comm σ hσ.invol o12
  have n1 : herm σ u1 u1 = herm σ u0 u0 := herm_mulVec_isometry hw u0 u0
  have n2 : herm σ u2 u2 = herm σ u0 u0 := (herm_mulVec_isometry hw u1 u1).trans n1
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hω12 : ω ≠ ω ^ 2 := fun h =>
    hω1 (mul_left_cancel₀ hω0 (by rw [mul_one, ← pow_two]; exact h.symm))
  have hli : LinearIndependent K ![u0, u1, u2] := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' y) ![1, ω, ω ^ 2] ?_ _ ?_
    · intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (simp [hω1, hω1.symm, hω2, hω2.symm, hω12, hω12.symm] at hij)
    · intro i
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
      · fin_cases i
        · simpa using e0
        · simpa using e1
        · simpa using e2
      · fin_cases i
        · exact hv
        · exact hw0
        · exact hw1
  have hspan : Submodule.span K (Set.range ![u0, u1, u2]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hν : herm σ u0 u0 ≠ 0 := by
    intro h0
    apply hv
    apply eq_zero_of_herm σ
    intro x
    have hx : x ∈ Submodule.span K (Set.range ![u0, u1, u2]) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      fin_cases i
      · exact h0
      · exact o01
      · exact o02
    | zero => exact herm_zero_right σ _
    | add a b _ _ h1 h2 => rw [herm_add_right, h1, h2, add_zero]
    | smul c a _ h1 => rw [herm_smul_right, h1, mul_zero]
  obtain ⟨c, hc⟩ := exists_smul_norm_one hσ hν
  rw [herm_smul_left, herm_smul_right] at hc
  have hc' : c * (σ c * herm σ u0 u0) = 1 := by rw [← hc]; ring
  set s : Fin 3 → Fin 3 → K := ![c • u0, c • u1, c • u2] with hs
  have hso : ∀ i j, herm σ (s i) (s j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hs, herm_smul_left, herm_smul_right, o01, o02, o10, o12, o20, o21, n1, n2, hc']
  have sy : ∀ j, y *ᵥ s j = ![1, ω, ω ^ 2] j • s j := by
    intro j
    fin_cases j
    · simp [hs, mulVec_smul, e0]
    · simp [hs, mulVec_smul, e1, smul_comm c]
    · simp [hs, mulVec_smul, e2, smul_comm c]
  have wc0 : w *ᵥ s 0 = s 1 := by simp [hs, mulVec_smul, hu1, hu0]
  have wc1 : w *ᵥ s 1 = s 2 := by simp [hs, mulVec_smul, hu2]
  have wc2 : w *ᵥ s 2 = b • s 0 := by
    show w *ᵥ (c • u2) = b • (c • u0)
    rw [mulVec_smul, hu2, hu1, hw3v, smul_comm]
  refine ⟨Matrix.of fun i j => s j i, conjTr_mul_of_orthonormal s hso,
    mul_of_cols y s _ sy, ?_⟩
  ext i j
  fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using congrFun wc0 i
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using congrFun wc1 i
  · simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct, mul_comm] using
      congrFun wc2 i

end CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.RankTwoGU
