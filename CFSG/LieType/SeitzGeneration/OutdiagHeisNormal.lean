module

public import CFSG.LieType.SeitzGeneration.OutdiagBasic

public section

namespace CFSG.LieType.SeitzGeneration

open Module Matrix

variable {F : Type*} [Field F]

theorem mem_FixSL_conj {n : ℕ} {P : GL (Fin n) F} {M N : Matrix (Fin n) (Fin n) F}
    (h : M * (P : Matrix (Fin n) (Fin n) F) = (P : Matrix (Fin n) (Fin n) F) * N)
    {k : SpecialLinearGroup (Fin n) F} (hk : k ∈ FixSL N) : conjUnit P k ∈ FixSL M := by
  obtain ⟨ζ, hζ⟩ := hk
  refine ⟨ζ, ?_⟩
  have hPi : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * P = 1 := Units.inv_mul P
  have hiP : (P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := Units.mul_inv P
  have hM : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M =
      N * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    calc ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * M
        = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (M * P) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc, hiP, Matrix.mul_one]
      _ = _ := by rw [h, ← Matrix.mul_assoc, hPi, Matrix.one_mul]
  rw [conjUnit_coe]
  calc M * ((P : Matrix (Fin n) (Fin n) F) * k * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      = (M * P) * k * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        simp only [Matrix.mul_assoc]
    _ = P * (N * k) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [h]; simp only [Matrix.mul_assoc]
    _ = ζ • (P * (k * N) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        rw [hζ, Matrix.mul_smul, Matrix.smul_mul]
    _ = ζ • ((P * k * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * M) := by
        congr 1
        calc (P : Matrix (Fin n) (Fin n) F) * (k * N) *
              ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
            = P * k * (N * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [← hM]; simp only [Matrix.mul_assoc]

theorem exists_heisenberg_basis_gl {x y : GL (Fin 3) F} {ω α : F} (hω : IsPrimitiveRoot ω 3)
    (hyx : (y : Matrix (Fin 3) (Fin 3) F) * x = ω • ((x : Matrix (Fin 3) (Fin 3) F) * y))
    (hy3 : (y : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1)
    (hx3 : (x : Matrix (Fin 3) (Fin 3) F) ^ 3 = α • 1) :
    ∃ (P : GL (Fin 3) F) (ξ : F), ξ ^ 3 = 1 ∧
      (y : Matrix (Fin 3) (Fin 3) F) * P = P * diagonal ![ξ, ξ * ω, ξ * ω ^ 2] ∧
      (x : Matrix (Fin 3) (Fin 3) F) * P = P * !![0, 0, α; 1, 0, 0; 0, 1, 0] := by
  classical
  set X : Matrix (Fin 3) (Fin 3) F := (x : Matrix (Fin 3) (Fin 3) F) with hX
  set Y : Matrix (Fin 3) (Fin 3) F := (y : Matrix (Fin 3) (Fin 3) F) with hY
  obtain ⟨ξ, v, hξ3, hv0, hYv⟩ := exists_eigenvector_of_pow_eq_one (p := 3) (by norm_num)
    ⟨ω, hω⟩ (by norm_num) hy3
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ3
  have hYX : ∀ k : ℕ, Y * X ^ k = ω ^ k • (X ^ k * Y) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc Y * X ^ (k + 1) = (Y * X ^ k) * X := by rw [pow_succ, Matrix.mul_assoc]
        _ = ω ^ k • (X ^ k * (Y * X)) := by
          rw [ih, Matrix.smul_mul, Matrix.mul_assoc]
        _ = ω ^ (k + 1) • (X ^ (k + 1) * Y) := by
          rw [hyx, Matrix.mul_smul, smul_smul, pow_succ ω k, pow_succ X k, mul_comm (ω ^ k) ω,
            Matrix.mul_assoc]
  let u : Fin 3 → (Fin 3 → F) := fun k => (X ^ (k : ℕ)).mulVec v
  have hYu : ∀ k : Fin 3, Y.mulVec (u k) = (ω ^ (k : ℕ) * ξ) • u k := by
    intro k
    simp only [u]
    rw [Matrix.mulVec_mulVec, hYX, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hYv,
      Matrix.mulVec_smul, smul_smul]
  have hu0 : ∀ k : Fin 3, u k ≠ 0 := by
    intro k hk
    apply hv0
    have h1 : ((x ^ (k : ℕ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = 0 := by
      rw [Units.val_pow_eq_pow_val]; exact hk
    have := congrArg (((x ^ (k : ℕ))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec h1
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  have hinj : Function.Injective (fun k : Fin 3 => ω ^ (k : ℕ) * ξ) := by
    intro k l h
    have h' : ω ^ (k : ℕ) = ω ^ (l : ℕ) := mul_right_cancel₀ hξ0 h
    exact Fin.ext (hω.pow_inj k.2 l.2 h')
  have hli : LinearIndependent F u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' Y)
      (fun k : Fin 3 => ω ^ (k : ℕ) * ξ) hinj u
      (fun k => ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hYu k, hu0 k⟩)
  let b : Basis (Fin 3) F (Fin 3 → F) := basisOfLinearIndependentOfCardEqFinrank' u hli (by simp)
  have hb : ∀ k, b k = u k := fun k => by simp [b]
  set P : GL (Fin 3) F := basisUnit b with hP
  have hPe : ∀ j : Fin 3, ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Pi.single j 1) =
      u j := fun j => by rw [hP, basisUnit_mulVec_single, one_smul, hb]
  obtain ⟨hX3⟩ : Nonempty (X ^ 3 = α • (1 : Matrix (Fin 3) (Fin 3) F)) := ⟨hx3⟩
  have hu0' : u 0 = v := by simp [u]
  have hu1' : u 1 = X.mulVec v := by simp [u]
  have hu2' : u 2 = (X ^ 2).mulVec v := by simp [u]
  have hXu0 : X.mulVec (u 0) = u 1 := by rw [hu0', hu1']
  have hXu1 : X.mulVec (u 1) = u 2 := by
    rw [hu1', hu2', Matrix.mulVec_mulVec, pow_two]
  have hXu2 : X.mulVec (u 2) = α • u 0 := by
    have h1 : X * X ^ 2 = X ^ 3 := by rw [← pow_succ']
    rw [hu2', Matrix.mulVec_mulVec, h1, hX3, Matrix.smul_mulVec, Matrix.one_mulVec, hu0']
  have hPe2 : ∀ (j : Fin 3) (c : F),
      ((P : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Pi.single j c) = c • u j :=
    fun j c => by rw [hP, basisUnit_mulVec_single, hb]
  refine ⟨P, ξ, hξ3, matrix_eq_of_mulVec_single fun j => ?_, matrix_eq_of_mulVec_single fun j => ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe, Matrix.diagonal_mulVec_single, hPe2,
      hYu j, mul_one]
    fin_cases j <;> simp [mul_comm]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPe]
    fin_cases j
    · simp only [Fin.zero_eta]
      have hC : (!![0, 0, α; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).mulVec
          (Pi.single 0 1) = Pi.single 1 1 := by
        ext i; fin_cases i <;> simp
      rw [hC, hPe, hXu0]
    · simp only [Fin.mk_one]
      have hC : (!![0, 0, α; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).mulVec
          (Pi.single 1 1) = Pi.single 2 1 := by
        ext i; fin_cases i <;> simp
      rw [hC, hPe, hXu1]
    · simp only [Fin.reduceFinMk]
      have hC : (!![0, 0, α; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F).mulVec
          (Pi.single 2 1) = Pi.single 0 α := by
        ext i; fin_cases i <;> simp
      rw [hC, hPe2, hXu2]

end CFSG.LieType.SeitzGeneration
