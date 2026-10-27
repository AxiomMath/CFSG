module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z2A5Iso

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Module Matrix CFSG.LocalAnalysis.ComponentInitial

theorem psl35_graph_fixed_order_four {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 5)
    (A : GL (Fin 3) F) (hA : (A : Matrix (Fin 3) (Fin 3) F)ᵀ = A) :
    ∃ x : LinearFlag.projectiveSL 3 F,
      LinearFlag.conjAut 3 F A (LinearFlag.dualAut 3 F x) = x ∧ orderOf x = 4 := by
  classical
  have h5 : (5 : F) = 0 := by
    have := FiniteField.cast_card_eq_zero F
    rwa [hF, Nat.cast_ofNat] at this
  have h23 : (2 : F) * 3 = 1 := by linear_combination h5
  have h3 : (3 : F) ≠ 0 := fun h => by rw [h] at h23; simp at h23
  set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdetA : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp A.isUnit
    exact this.ne_zero
  have hsymm : M.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hA
  have hnd : M.toBilin'.Nondegenerate :=
    Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_of_det_ne_zero hdetA)
  obtain ⟨b, y, hiso, hy0, hy1, hy2⟩ :=
    exists_isometry_two_three (W := Fin 3 → F) hF (by simp) M.toBilin' hsymm hnd
  set L : (Fin 3 → F) →ₗ[F] (Fin 3 → F) := y.toLinearMap with hL
  set Y : Matrix (Fin 3) (Fin 3) F := LinearMap.toMatrix' L with hY
  have hYv : ∀ v, Y *ᵥ v = L v := fun v => by rw [hY, LinearMap.toMatrix'_mulVec]
  have hLy : ∀ v, L v = y v := fun v => rfl
  have hYAY : Yᵀ * M * Y = M := by
    ext i j
    have h1 := Matrix.toBilin'_single (Yᵀ * M * Y) i j
    rw [← Matrix.toBilin'_comp] at h1
    rw [← h1, ← Matrix.toBilin'_single M i j]
    have := hiso (Pi.single i 1) (Pi.single j 1)
    simpa [Matrix.toLin'_apply, hYv, hLy] using this
  have hL0 : L (b 0) = (2 : F) • b 0 := hy0
  have hL1 : L (b 1) = (3 : F) • b 1 := hy1
  have hL2 : L (b 2) = b 2 := hy2
  have hL4 : L ^ 4 = 1 := by
    refine b.ext fun i => ?_
    have e16 : (2 : F) * 2 * 2 * 2 = 1 := by linear_combination 3 * h5
    have e81 : (3 : F) * 3 * 3 * 3 = 1 := by linear_combination 16 * h5
    have e16' : (2 : F) * (2 * (2 * 2)) = 1 := by linear_combination 3 * h5
    have e81' : (3 : F) * (3 * (3 * 3)) = 1 := by linear_combination 16 * h5
    fin_cases i
    · simp [pow_succ, Module.End.mul_apply, hL0, smul_smul, e16, e16']
    · simp [pow_succ, Module.End.mul_apply, hL1, smul_smul, e81, e81']
    · simp [pow_succ, Module.End.mul_apply, hL2]
  have hL22 : (L ^ 2) (b 0) = (4 : F) • b 0 := by
    rw [pow_two, Module.End.mul_apply, hL0, map_smul, hL0, smul_smul]
    norm_num
  have hL2b : (L ^ 2) (b 2) = b 2 := by
    rw [pow_two, Module.End.mul_apply, hL2, hL2]
  have hpow : ∀ n : ℕ, Y ^ n = LinearMap.toMatrix' (L ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ, ih, LinearMap.toMatrix'_mul]
  have hY4 : Y ^ 4 = 1 := by rw [hpow, hL4]; simp
  have hdet : Y.det = 1 := by
    rw [hY, LinearMap.det_toMatrix', ← LinearMap.det_toMatrix b L]
    have : LinearMap.toMatrix b b L = Matrix.diagonal ![2, 3, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [LinearMap.toMatrix_apply, hL0, hL1, hL2, Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal, Fin.prod_univ_three]
    simpa using h23
  have hYscalar : ∀ c : F, Y ^ 2 ≠ Matrix.scalar (Fin 3) c := by
    intro c hc
    have hv : ∀ v, (Y ^ 2) *ᵥ v = (L ^ 2) v := by
      intro v
      rw [hpow, LinearMap.toMatrix'_mulVec]
    have h0 := hv (b 0)
    have h2 := hv (b 2)
    have hsc : ∀ v : Fin 3 → F, (Matrix.scalar (Fin 3) c) *ᵥ v = c • v := by
      intro v; ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rw [hc, hsc, hL22] at h0
    rw [hc, hsc, hL2b] at h2
    have hc4 : c = 4 := smul_left_injective F (b.ne_zero 0) h0
    have hc1 : c = 1 := by
      have := smul_left_injective F (b.ne_zero 2) (h2.trans (one_smul F (b 2)).symm)
      exact this
    apply h3
    linear_combination hc4.symm.trans hc1
  have hdetT : (Yᵀ).det = 1 := by rw [Matrix.det_transpose]; exact hdet
  let g : Matrix.SpecialLinearGroup (Fin 3) F := ⟨Yᵀ, hdetT⟩
  have hgc : (g : Matrix (Fin 3) (Fin 3) F) = Yᵀ := rfl
  have hg4 : g ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← Matrix.transpose_pow, hY4]
    simp
  have hg2 : g ^ 2 ∉ LinearFlag.scalars 3 F := by
    rintro ⟨c, -, hc⟩
    rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← Matrix.transpose_pow] at hc
    apply hYscalar (c : F)
    have := congrArg Matrix.transpose hc
    rw [Matrix.transpose_transpose] at this
    rw [this]
    simp [Matrix.scalar_apply, Matrix.diagonal_transpose]
  refine ⟨LinearFlag.proj 3 F g, ?_, ?_⟩
  · rw [LinearFlag.dualAut_proj, LinearFlag.conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation]
    have hN : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * Yᵀ =
        1 := by
      rw [← hgc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
    have hNt := congrArg Matrix.transpose hN
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at hNt
    have hAinv : M * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := A.mul_inv
    have h1 : M * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F)ᵀ = Yᵀ * M := by
      calc _ = (Yᵀ * M * Y) *
            ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ := by
            rw [hYAY]
        _ = Yᵀ * M *
            (Y * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ) := by
            rw [Matrix.mul_assoc]
        _ = Yᵀ * M := by rw [hNt, Matrix.mul_one]
    rw [Matrix.SpecialLinearGroup.coe_transpose, h1, Matrix.mul_assoc, hAinv, Matrix.mul_one]
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := LinearFlag.proj 3 F g) ?_ ?_
    · simpa using this
    · intro h
      apply hg2
      rw [← LinearFlag.ker_proj, MonoidHom.mem_ker, map_pow]
      simpa using h
    · rw [← map_pow]
      simp [hg4]

end CFSG.OddStandard.SmallF3.Omega
