module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalLinearLagrangianSupply

public noncomputable section

namespace CFSG.SeitzReduction.ClassicalLinear.Lagrangian

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem basis_dotProduct_dualVec {ι : Type*} [DecidableEq ι] (b : Module.Basis ι K (Fin n → K))
    (m k : ι) : b m ⬝ᵥ dualVec b k = if m = k then 1 else 0 := by
  rw [dotProduct_comm, dualVec_dotProduct_basis]

section Two

variable (b : Module.Basis (Fin 2 ⊕ (Fin 2 ⊕ Fin 0)) K (Fin n → K))

@[expose] def formMat : Matrix (Fin n) (Fin n) K :=
  vecMulVec (b (.inl 0)) (b (.inr (.inl 1))) + vecMulVec (b (.inl 1)) (b (.inr (.inl 0))) +
    vecMulVec (b (.inr (.inl 0))) (b (.inl 1)) + vecMulVec (b (.inr (.inl 1))) (b (.inl 0))

@[expose] def formMatInv : Matrix (Fin n) (Fin n) K :=
  vecMulVec (dualVec b (.inr (.inl 1))) (dualVec b (.inl 0)) +
    vecMulVec (dualVec b (.inr (.inl 0))) (dualVec b (.inl 1)) +
    vecMulVec (dualVec b (.inl 1)) (dualVec b (.inr (.inl 0))) +
    vecMulVec (dualVec b (.inl 0)) (dualVec b (.inr (.inl 1)))

theorem formMat_transpose : (formMat b)ᵀ = formMat b := by
  simp only [formMat, transpose_add, transpose_vecMulVec]
  abel

theorem formMatInv_transpose : (formMatInv b)ᵀ = formMatInv b := by
  simp only [formMatInv, transpose_add, transpose_vecMulVec]
  abel

theorem formMat_mulVec_dualVec (k : Fin 2 ⊕ (Fin 2 ⊕ Fin 0)) :
    formMat b *ᵥ dualVec b k = (match k with
      | .inl 0 => b (.inr (.inl 1))
      | .inl 1 => b (.inr (.inl 0))
      | .inr (.inl 0) => b (.inl 1)
      | .inr (.inl 1) => b (.inl 0)) := by
  rcases k with i | i | i
  · fin_cases i <;> simp [formMat, add_mulVec, vecMulVec_mulVec', basis_dotProduct_dualVec]
  · fin_cases i <;> simp [formMat, add_mulVec, vecMulVec_mulVec', basis_dotProduct_dualVec]
  · exact i.elim0

theorem formMatInv_mulVec_basis (k : Fin 2 ⊕ (Fin 2 ⊕ Fin 0)) :
    formMatInv b *ᵥ b k = (match k with
      | .inl 0 => dualVec b (.inr (.inl 1))
      | .inl 1 => dualVec b (.inr (.inl 0))
      | .inr (.inl 0) => dualVec b (.inl 1)
      | .inr (.inl 1) => dualVec b (.inl 0)) := by
  rcases k with i | i | i
  · fin_cases i <;> simp [formMatInv, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  · fin_cases i <;> simp [formMatInv, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  · exact i.elim0

theorem formMat_mul_formMatInv : formMat b * formMatInv b = 1 := by
  refine matrix_eq_of_mulVec_basis b fun m => ?_
  rw [← mulVec_mulVec, one_mulVec, formMatInv_mulVec_basis]
  rcases m with i | i | i
  · fin_cases i <;> simp [formMat_mulVec_dualVec]
  · fin_cases i <;> simp [formMat_mulVec_dualVec]
  · exact i.elim0

@[expose] def formGL : GL (Fin n) K :=
  ⟨formMat b, formMatInv b, formMat_mul_formMatInv b, mul_eq_one_comm.mp (formMat_mul_formMatInv b)⟩

theorem coe_formGL : ((formGL b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = formMat b := rfl

theorem coe_formGL_inv :
    (((formGL b)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = formMatInv b := rfl

theorem inverseTranspose_formGL :
    GeneralLinearGroup.inverseTranspose (formGL b) = (formGL b)⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose, coe_formGL_inv, formMatInv_transpose]

@[expose] def dualPrime : MulAut (projectiveSL n K) := conjAut n K (formGL b) * dualAut n K

theorem dualPrime_mul_self : dualPrime b * dualPrime b = 1 := by
  obtain ⟨-, -, -, hdd, hdc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  rw [dualPrime, show conjAut n K (formGL b) * dualAut n K * (conjAut n K (formGL b) *
    dualAut n K) = conjAut n K (formGL b) * (dualAut n K * conjAut n K (formGL b) *
      dualAut n K) by group, hdc, inverseTranspose_formGL, ← map_mul, mul_inv_cancel, map_one]

theorem dualPrime_apply_proj_of_isometry {g : SpecialLinearGroup (Fin n) K}
    (hg : (g : Matrix (Fin n) (Fin n) K) * formMat b * (g : Matrix (Fin n) (Fin n) K)ᵀ =
      formMat b) :
    dualPrime b (proj n K g) = proj n K g := by
  rw [dualPrime, MulAut.mul_apply, dualAut_proj, conjAut_proj]
  congr 1
  refine sl_ext_of_coe ?_
  rw [coe_slConjugation, coe_formGL, coe_formGL_inv]
  set G := (g : Matrix (Fin n) (Fin n) K)
  set Gi := ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hGi : Gi * G = 1 := congrArg Subtype.val (inv_mul_cancel g)
  change formMat b * Giᵀ * formMatInv b = G
  have h1 : G * formMat b = formMat b * Giᵀ := by
    calc G * formMat b = G * formMat b * (Gi * G)ᵀ := by rw [hGi, transpose_one, Matrix.mul_one]
      _ = G * formMat b * Gᵀ * Giᵀ := by rw [transpose_mul, Matrix.mul_assoc _ Gᵀ]
      _ = formMat b * Giᵀ := by rw [hg]
  rw [← h1, Matrix.mul_assoc, formMat_mul_formMatInv, Matrix.mul_one]

theorem rankOne_isometry {x a y : Fin n → K} (h : a ⬝ᵥ x = 0)
    (hJa : formMat b *ᵥ a = y) (haJ : a ᵥ* formMat b = y) (hya : y ⬝ᵥ a = 0)
    (hxy : vecMulVec x y + vecMulVec y x = 0) :
    ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * formMat b *
      ((rankOne x a h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
        formMat b := by
  rw [coe_rankOne, transpose_add, transpose_one, transpose_vecMulVec]
  have e1 : vecMulVec x a * formMat b = vecMulVec x y := by rw [vecMulVec_mul, haJ]
  have e2 : formMat b * vecMulVec a x = vecMulVec y x := by rw [mul_vecMulVec, hJa]
  have e3 : vecMulVec x a * formMat b * vecMulVec a x = 0 := by
    rw [e1, vecMulVec_mul_vecMulVec, hya, zero_smul, vecMulVec_zero]
  calc (1 + vecMulVec x a) * formMat b * (1 + vecMulVec a x)
      = formMat b + vecMulVec x a * formMat b + formMat b * vecMulVec a x +
          vecMulVec x a * formMat b * vecMulVec a x := by noncomm_ring
    _ = formMat b := by rw [e3, e1, e2, add_zero, add_assoc, hxy, add_zero]

theorem neg_vec_eq [CharP K 2] (v : Fin n → K) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul K, CharTwo.two_eq_zero, zero_smul]

theorem vecMulVec_add_vecMulVec_smul_self [CharP K 2] (x : Fin n → K) (c : K) :
    vecMulVec x (c • x) + vecMulVec (c • x) x = 0 := by
  rw [vecMulVec_smul, smul_vecMulVec, ← two_smul K, CharTwo.two_eq_zero, zero_smul]

theorem vecMul_formMat (a : Fin n → K) : a ᵥ* formMat b = formMat b *ᵥ a := by
  rw [← mulVec_transpose, formMat_transpose]

theorem offDiag_isometry [CharP K 2] {i j : Fin 2} (hij : i ≠ j) (c : K)
    (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0) :
    ((rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * formMat b *
      ((rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ = formMat b := by
  have hJ : formMat b *ᵥ dualVec b (.inl i) = b (.inr (.inl j)) := by
    rw [formMat_mulVec_dualVec]
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | rfl
  refine rankOne_isometry b h hJ (by rw [vecMul_formMat, hJ]) ?_ ?_
  · rw [dotProduct_comm, dualVec_inl_dotProduct_inr]
  · rw [add_comm]
    exact vecMulVec_add_vecMulVec_smul_self (b (.inr (.inl j))) c

theorem extra_isometry [CharP K 2]
    (h : (dualVec b (.inl 1) - dualVec b (.inl 0)) ⬝ᵥ
      (b (.inr (.inl 0)) + b (.inr (.inl 1))) = 0) :
    ((rankOne (b (.inr (.inl 0)) + b (.inr (.inl 1))) (dualVec b (.inl 1) - dualVec b (.inl 0)) h :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * formMat b *
      ((rankOne (b (.inr (.inl 0)) + b (.inr (.inl 1))) (dualVec b (.inl 1) - dualVec b (.inl 0))
        h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = formMat b := by
  have hJ : formMat b *ᵥ (dualVec b (.inl 1) - dualVec b (.inl 0)) =
      b (.inr (.inl 0)) + b (.inr (.inl 1)) := by
    rw [mulVec_sub, formMat_mulVec_dualVec, formMat_mulVec_dualVec, sub_eq_add_neg,
      neg_vec_eq]
  refine rankOne_isometry b h hJ (by rw [vecMul_formMat, hJ]) (by rw [dotProduct_comm]; exact h) ?_
  have := vecMulVec_add_vecMulVec_smul_self (b (.inr (.inl 0)) + b (.inr (.inl 1))) (1 : K)
  rwa [one_smul] at this

theorem leviT_isometry [CharP K 2] :
    ((leviT b (show (0 : Fin 2) ≠ 1 by decide) 1 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) * formMat b *
      ((leviT b (show (0 : Fin 2) ≠ 1 by decide) 1 : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K)ᵀ = formMat b := by
  rw [coe_leviT, one_smul]
  have hQJ : leviQ b 0 1 * formMat b =
      vecMulVec (b (.inl 0)) (b (.inr (.inl 0))) + vecMulVec (b (.inr (.inl 0))) (b (.inl 0)) := by
    rw [leviQ, Matrix.add_mul, vecMulVec_mul, vecMulVec_mul, vecMul_formMat, vecMul_formMat,
      formMat_mulVec_dualVec, formMat_mulVec_dualVec]
  have hJQ : formMat b * (leviQ b 0 1)ᵀ =
      vecMulVec (b (.inl 0)) (b (.inr (.inl 0))) + vecMulVec (b (.inr (.inl 0))) (b (.inl 0)) := by
    rw [← formMat_transpose b, ← transpose_mul, hQJ, transpose_add, transpose_vecMulVec,
      transpose_vecMulVec, add_comm]
  have hQJQ : leviQ b 0 1 * formMat b * (leviQ b 0 1)ᵀ = 0 := by
    rw [hQJ, leviQ, transpose_add, transpose_vecMulVec, transpose_vecMulVec]
    simp [Matrix.add_mul, Matrix.mul_add, vecMulVec_mul_vecMulVec, basis_dotProduct_dualVec]
  rw [transpose_add, transpose_one]
  calc (1 + leviQ b 0 1) * formMat b * (1 + (leviQ b 0 1)ᵀ)
      = formMat b + (leviQ b 0 1 * formMat b + formMat b * (leviQ b 0 1)ᵀ) +
          leviQ b 0 1 * formMat b * (leviQ b 0 1)ᵀ := by noncomm_ring
    _ = formMat b := by
      rw [hQJQ, hQJ, hJQ, add_zero, ← two_smul K, CharTwo.two_eq_zero, zero_smul, add_zero]

theorem sq_eq_one_of_fix_dualAut_two [Finite K] [CharP K 2] (hn : 3 ≤ n) {A : GL (Fin n) K}
    {φ : K ≃+* K}
    (hoff : ∀ i j : Fin 2, i ≠ j → ∀ (c : K)
      (h : dualVec b (.inl i) ⬝ᵥ (c • b (.inr (.inl j))) = 0),
      (conjAut n K A * fieldAut n K φ * dualAut n K)
          (proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h)) =
        proj n K (rankOne (c • b (.inr (.inl j))) (dualVec b (.inl i)) h))
    (hext : ∀ h : (dualVec b (.inl 1) - dualVec b (.inl 0)) ⬝ᵥ
        (b (.inr (.inl 0)) + b (.inr (.inl 1))) = 0,
      (conjAut n K A * fieldAut n K φ * dualAut n K) (proj n K (rankOne (b (.inr (.inl 0)) +
          b (.inr (.inl 1))) (dualVec b (.inl 1) - dualVec b (.inl 0)) h)) =
        proj n K (rankOne (b (.inr (.inl 0)) + b (.inr (.inl 1)))
          (dualVec b (.inl 1) - dualVec b (.inl 0)) h))
    (hlevi : (conjAut n K A * fieldAut n K φ * dualAut n K)
        (proj n K (leviT b (show (0 : Fin 2) ≠ 1 by decide) 1)) =
      proj n K (leviT b (show (0 : Fin 2) ≠ 1 by decide) 1)) :
    (conjAut n K A * fieldAut n K φ * dualAut n K) ^ 2 = 1 := by
  obtain ⟨-, -, hfc, hdd, hdc, -⟩ := standard_automorphism_transport (n := n) (K := K)
  set A' := A * GeneralLinearGroup.map (φ : K →+* K)
    (GeneralLinearGroup.inverseTranspose (formGL b)) with hA'
  have hβδ : conjAut n K A * fieldAut n K φ * dualAut n K * dualPrime b =
      conjAut n K A' * fieldAut n K φ := by
    rw [dualPrime, hA', map_mul, ← hfc φ, show conjAut n K A * fieldAut n K φ * dualAut n K *
      (conjAut n K (formGL b) * dualAut n K) = conjAut n K A * fieldAut n K φ *
        (dualAut n K * conjAut n K (formGL b) * dualAut n K) by group, hdc]
    group
  have hfix' : ∀ g : SpecialLinearGroup (Fin n) K,
      (conjAut n K A * fieldAut n K φ * dualAut n K) (proj n K g) = proj n K g →
      (g : Matrix (Fin n) (Fin n) K) * formMat b * (g : Matrix (Fin n) (Fin n) K)ᵀ =
        formMat b →
      (conjAut n K A' * fieldAut n K φ) (proj n K g) = proj n K g := by
    intro g hg hgJ
    rw [← hβδ, MulAut.mul_apply, dualPrime_apply_proj_of_isometry b hgJ, hg]
  obtain ⟨rfl, κ, hκ, hW, hX⟩ := semilinear_rigid_of_fix b hn (i₀ := 0) (i₁ := 1) (by decide)
    (fun i j hij c h => hfix' _ (hoff i j hij c h) (offDiag_isometry b hij c h))
    (fun h => hfix' _ (hext h) (extra_isometry b h))
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hL : (A' : Matrix (Fin n) (Fin n) K) *
      ((leviT b h01 1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((leviT b h01 1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg Units.val (conj_map_eq_of_apply_eq hn (u := leviT b h01 1)
      (by rw [coe_leviT, one_smul, add_sub_cancel_left, leviQ_mul_self b h01])
      (hfix' _ hlevi (leviT_isometry b)))
  rw [coe_leviT, one_smul] at hL
  set Q := leviQ b 0 1 with hQ
  have hAQ : (A' : Matrix (Fin n) (Fin n) K) * Q = Q * (A' : Matrix (Fin n) (Fin n) K) := by
    have h2 : (A' : Matrix (Fin n) (Fin n) K) * (1 + Q) = (1 + Q) * A' := by
      calc (A' : Matrix (Fin n) (Fin n) K) * (1 + Q)
          = (A' : Matrix (Fin n) (Fin n) K) * (1 + Q) *
            (((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A') := by
            rw [inv_mul_self_val, Matrix.mul_one]
        _ = (A' : Matrix (Fin n) (Fin n) K) * (1 + Q) *
            ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A' := by
            simp only [Matrix.mul_assoc]
        _ = (1 + Q) * A' := by rw [hL]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h2
    exact add_left_cancel h2
  set Y := (A' : Matrix (Fin n) (Fin n) K) - κ • (1 : Matrix (Fin n) (Fin n) K) with hY
  have hA'Y : (A' : Matrix (Fin n) (Fin n) K) = κ • (1 : Matrix (Fin n) (Fin n) K) + Y := by
    rw [hY, add_sub_cancel]
  have hYmul : ∀ v, Y *ᵥ v = (A' : Matrix (Fin n) (Fin n) K) *ᵥ v - κ • v := fun v => by
    rw [hY, sub_mulVec, smul_mulVec, one_mulVec]
  have hYW : ∀ j, Y *ᵥ b (.inr (.inl j)) = 0 := fun j => by rw [hYmul, hW, sub_self]
  have hYX : ∀ v i, dualVec b (.inl i) ⬝ᵥ (Y *ᵥ v) = 0 := fun v i => by rw [hYmul]; exact hX v i
  have hYQ : Y * Q = Q * Y := by
    rw [hY, Matrix.sub_mul, Matrix.mul_sub, hAQ, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  obtain ⟨a, r, hYX1⟩ : ∃ a r : K,
      Y *ᵥ b (.inl 1) = a • b (.inr (.inl 0)) + r • b (.inr (.inl 1)) := by
    refine ⟨dualVec b (.inr (.inl 0)) ⬝ᵥ (Y *ᵥ b (.inl 1)),
      dualVec b (.inr (.inl 1)) ⬝ᵥ (Y *ᵥ b (.inl 1)), ?_⟩
    conv_lhs => rw [eq_sum_of_dualVec_inl_eq_zero b (hYX (b (.inl 1)))]
    rw [Fin.sum_univ_two]
  have hQX1 : Q *ᵥ b (.inl 1) = b (.inl 0) := by
    simp [hQ, leviQ, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  have hQW0 : Q *ᵥ b (.inr (.inl 0)) = 0 := by
    simp [hQ, leviQ, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  have hQW1 : Q *ᵥ b (.inr (.inl 1)) = b (.inr (.inl 0)) := by
    simp [hQ, leviQ, add_mulVec, vecMulVec_mulVec', dualVec_dotProduct_basis]
  have hYX0 : Y *ᵥ b (.inl 0) = r • b (.inr (.inl 0)) := by
    have h := congrArg (· *ᵥ b (.inl 1)) hYQ
    simp only [← mulVec_mulVec] at h
    rw [hQX1, hYX1, mulVec_add, mulVec_smul, mulVec_smul, hQW0, hQW1, smul_zero, zero_add] at h
    exact h
  have hYJ : Y * formMat b = vecMulVec (r • b (.inr (.inl 0))) (b (.inr (.inl 1))) +
      vecMulVec (a • b (.inr (.inl 0)) + r • b (.inr (.inl 1))) (b (.inr (.inl 0))) := by
    rw [formMat, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec,
      mul_vecMulVec, mul_vecMulVec, hYX0, hYX1, hYW, hYW, zero_vecMulVec, zero_vecMulVec,
      add_zero, add_zero]
  have hYJt : (Y * formMat b)ᵀ = Y * formMat b := by
    rw [hYJ]
    simp only [transpose_add, transpose_smul, transpose_vecMulVec, add_vecMulVec,
      smul_vecMulVec]
    abel
  have hJYt : formMat b * Yᵀ = Y * formMat b := by
    rw [← hYJt, transpose_mul, formMat_transpose]
  have hYJY : Y * formMat b * Yᵀ = 0 := by
    rw [Matrix.mul_assoc, hJYt, hYJ, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, mulVec_smul,
      mulVec_add, mulVec_smul, mulVec_smul, hYW, hYW, smul_zero, smul_zero, add_zero,
      zero_vecMulVec, zero_vecMulVec, add_zero]
  have hAJA : (A' : Matrix (Fin n) (Fin n) K) * formMat b * (A' : Matrix (Fin n) (Fin n) K)ᵀ =
      (κ * κ) • formMat b := by
    rw [hA'Y, transpose_add, transpose_smul, transpose_one]
    have e : (κ • (1 : Matrix (Fin n) (Fin n) K) + Y) * formMat b * (κ • 1 + Yᵀ) =
        (κ * κ) • formMat b + κ • (Y * formMat b + formMat b * Yᵀ) + Y * formMat b * Yᵀ := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul, smul_add]
      abel
    rw [e, hYJY, hJYt, add_zero, ← two_smul K (Y * formMat b), CharTwo.two_eq_zero, zero_smul,
      smul_zero, add_zero]
  set u : Kˣ := Units.mk0 κ hκ with hu
  have hJA : formGL b * GeneralLinearGroup.inverseTranspose A' =
      GeneralLinearGroup.scalar (Fin n) (u⁻¹ * u⁻¹) * A' * formGL b := by
    apply Units.ext
    set Ai := ((A'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    have hAi : Ai * (A' : Matrix (Fin n) (Fin n) K) = 1 := inv_mul_self_val A'
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_inverseTranspose,
      coe_formGL, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal]
    change formMat b * Aiᵀ = _
    have h1 : (A' : Matrix (Fin n) (Fin n) K) * formMat b = (κ * κ) • (formMat b * Aiᵀ) := by
      calc (A' : Matrix (Fin n) (Fin n) K) * formMat b
          = (A' : Matrix (Fin n) (Fin n) K) * formMat b *
              (Ai * (A' : Matrix (Fin n) (Fin n) K))ᵀ := by
            rw [hAi, transpose_one, Matrix.mul_one]
        _ = (A' : Matrix (Fin n) (Fin n) K) * formMat b * (A' : Matrix (Fin n) (Fin n) K)ᵀ *
            Aiᵀ := by rw [transpose_mul, Matrix.mul_assoc _ (A' : Matrix (Fin n) (Fin n) K)ᵀ]
        _ = (κ * κ) • (formMat b * Aiᵀ) := by rw [hAJA, Matrix.smul_mul]
    rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, h1, smul_smul, hu]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [show κ⁻¹ * κ⁻¹ * (κ * κ) = 1 by field_simp, one_smul]
  have hcomm : dualPrime b * conjAut n K A' = conjAut n K A' * dualPrime b := by
    have e1 : dualPrime b * conjAut n K A' = conjAut n K (formGL b) *
        (dualAut n K * conjAut n K A' * dualAut n K) * dualAut n K := by
      rw [dualPrime, show conjAut n K (formGL b) * (dualAut n K * conjAut n K A' * dualAut n K) *
        dualAut n K = conjAut n K (formGL b) * dualAut n K * conjAut n K A' *
          (dualAut n K * dualAut n K) by group, hdd, mul_one]
    rw [e1, hdc, ← map_mul, hJA, map_mul, map_mul, conjAut_scalar, one_mul, dualPrime]
    group
  have hβ : conjAut n K A * fieldAut n K 1 * dualAut n K = conjAut n K A' * dualPrime b := by
    calc conjAut n K A * fieldAut n K 1 * dualAut n K
        = conjAut n K A * fieldAut n K 1 * dualAut n K * (dualPrime b * dualPrime b) := by
          rw [dualPrime_mul_self, mul_one]
      _ = conjAut n K A * fieldAut n K 1 * dualAut n K * dualPrime b * dualPrime b := by group
      _ = conjAut n K A' * dualPrime b := by rw [hβδ, map_one, mul_one]
  rw [hβ, pow_two, show conjAut n K A' * dualPrime b * (conjAut n K A' * dualPrime b) =
    conjAut n K A' * (dualPrime b * conjAut n K A') * dualPrime b by group, hcomm,
    show conjAut n K A' * (conjAut n K A' * dualPrime b) * dualPrime b =
      conjAut n K A' * conjAut n K A' * (dualPrime b * dualPrime b) by group,
    dualPrime_mul_self, mul_one, ← pow_two]
  exact conjAut_sq_eq_one_of_mulVec b hκ hW hX

end Two

end CFSG.SeitzReduction.ClassicalLinear.Lagrangian
