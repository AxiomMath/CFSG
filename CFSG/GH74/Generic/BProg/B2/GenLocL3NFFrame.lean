module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NFAux

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG.LocalAnalysis.ComponentInitial Matrix

namespace GenLocL3NFFrame

variable {K : Type} [Field K]

theorem isDiag_inv_gl {x : GL (Fin 3) K} (h : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  refine GenLocL3NFAux.isDiag_of_mul_eq_one h ?_
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem isDiag_inverseTranspose {x : GL (Fin 3) K}
    (h : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((GeneralLinearGroup.inverseTranspose x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
  rw [GeneralLinearGroup.coe_inverseTranspose]
  exact (isDiag_inv_gl h).transpose

theorem isDiag_map_gl (σ : K ≃+* K) {x : GL (Fin 3) K}
    (h : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) :
    ((GeneralLinearGroup.map (σ : K →+* K) x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
  h.map (map_zero σ)

@[expose] def frameSet : Set (MulAut (LinearFlag.projectiveSL 3 K)) :=
  {y | ∃ (x : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ),
    ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧ ε ≤ 1 ∧
      y = LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε}

theorem isDiag_mul' {A B : Matrix (Fin 3) (Fin 3) K} (hA : A.IsDiag) (hB : B.IsDiag) :
    (A * B).IsDiag := by
  rw [← hA.diagonal_diag, ← hB.diagonal_diag, diagonal_mul_diagonal]
  exact isDiag_diagonal _

theorem mul_mem_frameSet {y₁ y₂ : MulAut (LinearFlag.projectiveSL 3 K)} (h₁ : y₁ ∈ frameSet)
    (h₂ : y₂ ∈ frameSet) : y₁ * y₂ ∈ frameSet := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := h₁
  obtain ⟨x', τ, e, hx', he, rfl⟩ := h₂
  have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have s1 := LinearFlag.fieldAut_mul_conjAut (n := 3) (K := K)
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K)
  have s3 := LinearFlag.dualAut_mul_fieldAut (n := 3) (K := K)
  have hd1 : ((x * GeneralLinearGroup.map (σ : K →+* K) x' : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
    rw [Units.val_mul]; exact isDiag_mul' hx (isDiag_map_gl σ hx')
  have hd2 : ((x * GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose x') :
      GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    rw [Units.val_mul]; exact isDiag_mul' hx (isDiag_map_gl σ (isDiag_inverseTranspose hx'))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl
  · refine ⟨_, σ * τ, 0, hd1, Nat.zero_le _, ?_⟩
    simp only [pow_zero, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ *
          (LinearFlag.conjAut 3 K x' * LinearFlag.fieldAut 3 K τ)
        = LinearFlag.conjAut 3 K x * (LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K x') *
          LinearFlag.fieldAut 3 K τ := by simp only [mul_assoc]
      _ = _ := by rw [s1]; simp only [mul_assoc]
  · refine ⟨_, σ * τ, 1, hd1, le_rfl, ?_⟩
    simp only [pow_zero, pow_one, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ *
          (LinearFlag.conjAut 3 K x' * LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K)
        = LinearFlag.conjAut 3 K x * (LinearFlag.fieldAut 3 K σ * LinearFlag.conjAut 3 K x') *
          LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K := by simp only [mul_assoc]
      _ = _ := by rw [s1]; simp only [mul_assoc]
  · refine ⟨_, σ * τ, 1, hd2, le_rfl, ?_⟩
    simp only [pow_zero, pow_one, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K *
          (LinearFlag.conjAut 3 K x' * LinearFlag.fieldAut 3 K τ)
        = LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * (LinearFlag.dualAut 3 K *
          LinearFlag.conjAut 3 K x') * LinearFlag.fieldAut 3 K τ := by simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K x * (LinearFlag.fieldAut 3 K σ *
          LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose x')) *
          (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K τ) := by rw [s2]; simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K x * (LinearFlag.conjAut 3 K
          (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose x')) *
          LinearFlag.fieldAut 3 K σ) * (LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K) := by
          rw [s1, s3]
      _ = _ := by simp only [mul_assoc]
  · refine ⟨_, σ * τ, 0, hd2, Nat.zero_le _, ?_⟩
    simp only [pow_zero, pow_one, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K *
          (LinearFlag.conjAut 3 K x' * LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K)
        = LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * (LinearFlag.dualAut 3 K *
          LinearFlag.conjAut 3 K x') * LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K := by
          simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K x * (LinearFlag.fieldAut 3 K σ *
          LinearFlag.conjAut 3 K (GeneralLinearGroup.inverseTranspose x')) *
          (LinearFlag.dualAut 3 K * LinearFlag.fieldAut 3 K τ) * LinearFlag.dualAut 3 K := by
          rw [s2]; simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K x * (LinearFlag.conjAut 3 K
          (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose x')) *
          LinearFlag.fieldAut 3 K σ) * (LinearFlag.fieldAut 3 K τ * LinearFlag.dualAut 3 K) *
          LinearFlag.dualAut 3 K := by rw [s1, s3]
      _ = LinearFlag.conjAut 3 K x * LinearFlag.conjAut 3 K
          (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose x')) *
          (LinearFlag.fieldAut 3 K σ * LinearFlag.fieldAut 3 K τ) *
          (LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K) := by simp only [mul_assoc]
      _ = _ := by rw [hδδ, mul_one]

theorem one_mem_frameSet : (1 : MulAut (LinearFlag.projectiveSL 3 K)) ∈ frameSet :=
  ⟨1, 1, 0, by rw [Units.val_one]; exact isDiag_one, Nat.zero_le _, by simp⟩

theorem inv_mem_frameSet {y : MulAut (LinearFlag.projectiveSL 3 K)} (h : y ∈ frameSet) :
    y⁻¹ ∈ frameSet := by
  obtain ⟨x, σ, ε, hx, hε, rfl⟩ := h
  have hδδ : LinearFlag.dualAut 3 K * LinearFlag.dualAut 3 K = 1 :=
    (LinearFlag.standard_automorphism_transport (K := K) (n := 3)).2.2.2.1
  have hδi : (LinearFlag.dualAut 3 K)⁻¹ = LinearFlag.dualAut 3 K := inv_eq_of_mul_eq_one_right hδδ
  have hy : (LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε)⁻¹ =
      LinearFlag.dualAut 3 K ^ ε * LinearFlag.fieldAut 3 K σ⁻¹ * LinearFlag.conjAut 3 K x⁻¹ := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, map_inv, map_inv, ← inv_pow, hδi]
    simp only [mul_assoc]
  rw [hy]
  have h1 : LinearFlag.dualAut 3 K ^ ε ∈ (frameSet (K := K)) :=
    ⟨1, 1, ε, by rw [Units.val_one]; exact isDiag_one, hε, by simp⟩
  have h2 : LinearFlag.fieldAut 3 K σ⁻¹ ∈ (frameSet (K := K)) :=
    ⟨1, σ⁻¹, 0, by rw [Units.val_one]; exact isDiag_one, Nat.zero_le _, by simp⟩
  have h3 : LinearFlag.conjAut 3 K x⁻¹ ∈ (frameSet (K := K)) :=
    ⟨x⁻¹, 1, 0, isDiag_inv_gl hx, Nat.zero_le _, by simp⟩
  exact mul_mem_frameSet (mul_mem_frameSet h1 h2) h3

theorem mem_frameStab_iff {y : MulAut (LinearFlag.projectiveSL 3 K)} :
    y ∈ frameStab 3 K ↔ ∃ (x : GL (Fin 3) K) (σ : K ≃+* K) (ε : ℕ),
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag ∧ ε ≤ 1 ∧
        y = LinearFlag.conjAut 3 K x * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ ε := by
  constructor
  · intro hy
    let S : Subgroup (MulAut (LinearFlag.projectiveSL 3 K)) :=
      { carrier := frameSet
        mul_mem' := fun ha hb => mul_mem_frameSet ha hb
        one_mem' := one_mem_frameSet
        inv_mem' := fun ha => inv_mem_frameSet ha }
    have hle : frameStab 3 K ≤ S := by
      rw [frameStab, Subgroup.closure_le]
      rintro _ ((⟨⟨x, hx⟩, rfl⟩ | ⟨σ, rfl⟩) | rfl)
      · exact ⟨x, 1, 0, hx, Nat.zero_le _, by simp⟩
      · exact ⟨1, σ, 0, by rw [Units.val_one]; exact isDiag_one, Nat.zero_le _, by simp⟩
      · exact ⟨1, 1, 1, by rw [Units.val_one]; exact isDiag_one, le_rfl, by simp⟩
    exact hle hy
  · rintro ⟨x, σ, ε, hx, -, rfl⟩
    exact mul_mem (mul_mem (GenLocL3NFAux.conjAut_mem_frameStab hx)
      (GenLocL3NFAux.fieldAut_mem_frameStab σ)) (pow_mem GenLocL3NFAux.dualAut_mem_frameStab ε)

end GenLocL3NFFrame

end CFSG.GH74.Generic.BProg.B2
