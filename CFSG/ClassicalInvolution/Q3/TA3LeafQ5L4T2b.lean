module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpTL4

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  PSpL TBlocks HBlocks StabL

variable {K : Type} [Field K]

theorem comm_of_conjAut_fix' (h4 : (4 : K) ≠ 0) (A : GL (Fin 4) K)
    {u : SpecialLinearGroup (Fin 4) K} (hu : (u : Matrix (Fin 4) (Fin 4) K).trace = 4)
    (h : conjAut 4 K A (proj 4 K u) = proj 4 K u) :
    (A : Matrix (Fin 4) (Fin 4) K) * u = u * A := by
  rw [conjAut_proj] at h
  obtain ⟨c, hc⟩ := InvClassL.eq_smul_of_proj_eq h.symm
  rw [coe_slConjugation] at hc
  have htr : (4 : K) = c * 4 := by
    have := congrArg Matrix.trace hc
    rwa [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, hu, Matrix.trace_smul, hu, smul_eq_mul] at this
  have hc1 : c = 1 := by
    have h0 : (4 : K) * (c - 1) = 0 := by linear_combination -htr
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 h4
    · linear_combination h0
  rw [hc1, one_smul] at hc
  calc (A : Matrix (Fin 4) (Fin 4) K) * u = A * u * ((A⁻¹ : GL (Fin 4) K) * A) := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    _ = u * A := by rw [← Matrix.mul_assoc, hc]

theorem invariant_of_conjAut_dual_fix' (h4 : (4 : K) ≠ 0) (A : GL (Fin 4) K)
    {u : SpecialLinearGroup (Fin 4) K} (hu : (u : Matrix (Fin 4) (Fin 4) K).trace = 4)
    (hu' : ((u⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).trace = 4)
    (h : (conjAut 4 K A * dualAut 4 K) (proj 4 K u) = proj 4 K u) :
    (u : Matrix (Fin 4) (Fin 4) K) * A * (u : Matrix (Fin 4) (Fin 4) K)ᵀ = A := by
  rw [MulAut.mul_apply, dualAut_proj, conjAut_proj] at h
  obtain ⟨c, hc⟩ := InvClassL.eq_smul_of_proj_eq h.symm
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose] at hc
  have htr : (4 : K) = c * 4 := by
    have := congrArg Matrix.trace hc
    rwa [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, Matrix.trace_transpose, hu', Matrix.trace_smul, hu,
      smul_eq_mul] at this
  have hc1 : c = 1 := by
    have h0 : (4 : K) * (c - 1) = 0 := by linear_combination -htr
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd h0 h4
    · linear_combination h0
  rw [hc1, one_smul] at hc
  calc (u : Matrix (Fin 4) (Fin 4) K) * A * (u : Matrix (Fin 4) (Fin 4) K)ᵀ
      = (A * ((u⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
          ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) * A *
            (u : Matrix (Fin 4) (Fin 4) K)ᵀ := by rw [hc]
    _ = A * (((u : Matrix (Fin 4) (Fin 4) K)) * ((u⁻¹ : SpecialLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K))ᵀ := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K),
          ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    _ = A := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one]

theorem conjAut_mul_dualAut_sq_of_alt (A : GL (Fin 4) K)
    (hA : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -A) :
    conjAut 4 K A * dualAut 4 K * (conjAut 4 K A * dualAut 4 K) = 1 := by
  obtain ⟨-, -, -, -, hδc, -⟩ := standard_automorphism_transport (K := K) (n := 4)
  set Ai : Matrix (Fin 4) (Fin 4) K := ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hAi
  have hAAi : (A : Matrix (Fin 4) (Fin 4) K) * Ai = 1 := by
    rw [hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hX : Aiᵀ = -Ai := by
    have h1 : Aiᵀ * (A : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAi, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    rw [hA, Matrix.mul_neg] at h1
    have h2 : Aiᵀ * (A : Matrix (Fin 4) (Fin 4) K) = -1 := neg_eq_iff_eq_neg.mp h1
    calc Aiᵀ = Aiᵀ * ((A : Matrix (Fin 4) (Fin 4) K) * Ai) := by rw [hAAi, Matrix.mul_one]
      _ = -Ai := by rw [← Matrix.mul_assoc, h2, Matrix.neg_mul, Matrix.one_mul]
  have h1 : A * Matrix.GeneralLinearGroup.inverseTranspose A =
      GeneralLinearGroup.scalar (Fin 4) (-1 : Kˣ) := by
    apply Units.ext
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose, ← hAi, hX, Matrix.mul_neg,
      hAAi, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_neg, Units.val_one,
      ← Matrix.smul_one_eq_diagonal, neg_one_smul]
  calc conjAut 4 K A * dualAut 4 K * (conjAut 4 K A * dualAut 4 K) =
      conjAut 4 K A * (dualAut 4 K * conjAut 4 K A * dualAut 4 K) := by simp only [mul_assoc]
    _ = conjAut 4 K (A * Matrix.GeneralLinearGroup.inverseTranspose A) := by
        rw [hδc, ← map_mul]
    _ = 1 := by rw [h1, conjAut_scalar]

theorem eq_conj_of_conj_eq {P : GL (Fin 4) K} {M D : Matrix (Fin 4) (Fin 4) K}
    (h : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * M * P = D) :
    M = (P : Matrix (Fin 4) (Fin 4) K) * D * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
  rw [← h]
  have hPP' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [Matrix.mul_assoc, hPP', Matrix.mul_one]

@[expose] def blkConj (P : GL (Fin 4) K) : Set (MulAut (projectiveSL 4 K)) :=
  {α | ∃ A : GL (Fin 4) K, ∃ x y : K,
    (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
      (P : Matrix (Fin 4) (Fin 4) K) = bd (x • 1) (y • 1) ∧ α = conjAut 4 K A}

theorem blkConj_comm (P : GL (Fin 4) K) : ∀ α ∈ blkConj P, ∀ β ∈ blkConj P, α * β = β * α := by
  rintro _ ⟨A, x, y, hA, rfl⟩ _ ⟨B, x', y', hB, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  have hPP : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hDD : bd (x • (1 : Matrix (Fin 2) (Fin 2) K)) (y • 1) * bd (x' • 1) (y' • 1) =
      bd (x' • (1 : Matrix (Fin 2) (Fin 2) K)) (y' • 1) * bd (x • 1) (y • 1) := by
    rw [bd_mul, bd_mul, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm x',
      smul_mul_smul_comm y', mul_comm x, mul_comm y]
  rw [Units.val_mul, Units.val_mul, eq_conj_of_conj_eq hA, eq_conj_of_conj_eq hB]
  calc (P : Matrix (Fin 4) (Fin 4) K) * bd (x • 1) (y • 1) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * bd (x' • 1) (y' • 1) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) =
      (P : Matrix (Fin 4) (Fin 4) K) * (bd (x • 1) (y • 1) * bd (x' • 1) (y' • 1)) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]
    _ = (P : Matrix (Fin 4) (Fin 4) K) * (bd (x' • 1) (y' • 1) * bd (x • 1) (y • 1)) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [hDD]
    _ = (P : Matrix (Fin 4) (Fin 4) K) * bd (x' • 1) (y' • 1) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
        ((P : Matrix (Fin 4) (Fin 4) K) * bd (x • 1) (y • 1) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) (P : Matrix (Fin 4) (Fin 4) K),
          hPP, Matrix.one_mul]

theorem dichotomy_t2 [Fintype K] (h4 : (4 : K) ≠ 0) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hf : Odd f) (P : GL (Fin 4) K) (α : MulAut (projectiveSL 4 K))
    (hα : α ^ 8 = 1)
    (hfix : ∀ x ∈ bdGens, α (proj 4 K (bdHom P x)) = proj 4 K (bdHom P x)) :
    α ∈ blkConj P ∨ α * α = 1 := by
  classical
  have hPP' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have g1 : ((slU (1 : K), (1 : SpecialLinearGroup (Fin 2) K)) :
      SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∈ bdGens :=
    Set.mem_insert _ _
  have g2 : ((slL (1 : K), (1 : SpecialLinearGroup (Fin 2) K)) :
      SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have g3 : (((1 : SpecialLinearGroup (Fin 2) K), slU (1 : K)) :
      SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have g4 : (((1 : SpecialLinearGroup (Fin 2) K), slL (1 : K)) :
      SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K) ∈ bdGens :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_singleton _)))
  have c1 : ((1 : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 :=
    Matrix.SpecialLinearGroup.coe_one
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
  obtain ⟨A, σ, e, he, rfl⟩ := hgen α
  have hσ := fieldAut_eq_one_of_pow hp hK hf A σ he (m := 2) (by simpa using hα)
  subst hσ
  simp only [map_one, mul_one] at hfix ⊢
  interval_cases e
  · left
    simp only [pow_zero, mul_one] at hfix ⊢
    have hc : ∀ x ∈ bdGens, (A : Matrix (Fin 4) (Fin 4) K) *
        ((bdHom P x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((bdHom P x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A :=
      fun x hx => comm_of_conjAut_fix' h4 A (trace_bdGens P hx).1 (hfix x hx)
    obtain ⟨A', hA'⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * P := ⟨_, rfl⟩
    have k1 := conj_comm_bd P (hc _ g1)
    have k2 := conj_comm_bd P (hc _ g2)
    have k3 := conj_comm_bd P (hc _ g3)
    have k4 := conj_comm_bd P (hc _ g4)
    rw [← hA'] at k1 k2 k3 k4
    simp only [c1] at k1 k2 k3 k4
    exact ⟨A, A' 0 0, A' 2 2, hA'.symm.trans (eq_of_comm_bd k1 k2 k3 k4), rfl⟩
  · right
    simp only [pow_one] at hfix ⊢
    have hi : ∀ x ∈ bdGens,
        ((bdHom P x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * A *
          ((bdHom P x : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ = A := by
      intro x hx
      apply invariant_of_conjAut_dual_fix' h4 A (trace_bdGens P hx).1 _ (hfix x hx)
      rw [← map_inv]
      exact (trace_bdGens P hx).2
    obtain ⟨A'', hA''⟩ : ∃ M : Matrix (Fin 4) (Fin 4) K,
        M = (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * A * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ :=
      ⟨_, rfl⟩
    have k1 := conj_inv_bd P (hi _ g1)
    have k2 := conj_inv_bd P (hi _ g2)
    have k3 := conj_inv_bd P (hi _ g3)
    have k4 := conj_inv_bd P (hi _ g4)
    rw [← hA''] at k1 k2 k3 k4
    simp only [c1] at k1 k2 k3 k4
    have hA''eq := eq_of_inv_bd k1 k2 k3 k4
    have hPPt : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)ᵀ * (P : Matrix (Fin 4) (Fin 4) K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
    have hAeq : (A : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * A'' *
        (P : Matrix (Fin 4) (Fin 4) K)ᵀ := by
      rw [hA'', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul, Matrix.mul_assoc,
        hPPt, Matrix.mul_one]
    have hAt : (A : Matrix (Fin 4) (Fin 4) K)ᵀ = -A := by
      rw [hAeq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hA''eq,
        transpose_bJ, Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
    exact conjAut_mul_dualAut_sq_of_alt A hAt

theorem noQ8Fix_t2 [Fintype K] (h4 : (4 : K) ≠ 0) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) (hf : Odd f) (P : GL (Fin 4) K) :
    NoQ8Fix (projectiveSL 4 K) ((proj 4 K).comp (bdHom P)).range :=
  noQ8Fix_of_dichotomy_pow (blkConj P) (blkConj_comm P) fun α hfix hα8 =>
    dichotomy_t2 h4 hp hK hf P α hα8 fun x _ => hfix _ ⟨x, rfl⟩

end CFSG.ClassicalInvolution.Q3.TA3.Q5L4
