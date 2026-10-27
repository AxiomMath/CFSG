module

public import CFSG.ClassicalInvolution.Phan.PhanS13CKer
public import CFSG.ClassicalInvolution.Phan.PhanS13CDet

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.PhanB3

section Main

variable {p f : ℕ} [Fact p.Prime]
  {hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2} {h2 : (2 : GaloisField p f) ≠ 0}
  {C : B2Coord hK (GaloisField p f) h2} {M : ModelB3 p f h2}
  {E : PhanFamilyB3 C (spinGroup (quadOdd 3 (GaloisField p f)))}
  [Algebra (GaloisField p f) (GaloisField p (2 * f))]
  {D : KDat (GaloisField p f) (GaloisField p (2 * f))}

theorem mem_torusSub_of_diag (S : Setup M E D) {h : spinGroup (quadOdd 3 (GaloisField p f))}
    {l₁ l₂ l₃ : GaloisField p (2 * f)} (n₁ : l₁ * D.τ l₁ = 1) (n₂ : l₂ * D.τ l₂ = 1)
    (n₃ : l₃ * D.τ l₃ = 1) (hd : l₁ * l₂ * l₃ = 1) (h₁ : actK h (vXi D) = l₁ • vXi D)
    (h₂ : actK h (vE2 D) = l₂ • vE2 D) (h₃ : actK h (vE3 D) = l₃ • vE3 D) :
    h ∈ torusSub E := by
  have h2F : (2 : GaloisField p f) ≠ 0 := h2
  have hν : D.τ l₃ * D.τ (D.τ l₃) = 1 := by rw [D.tau_tau]; linear_combination n₃
  obtain ⟨t, ht, e1, e2, e3⟩ := exists_torus01_eigen D S.good S.h2K S.h4 S.range S.n0 S.n1 S.tau
    l₁ (D.τ l₃) n₁ hν
  have hl₁ : l₁ ≠ 0 := left_ne_zero_of_mul_eq_one n₁
  have hl₂ : l₂ ≠ 0 := left_ne_zero_of_mul_eq_one n₂
  have hl₃ : l₃ ≠ 0 := left_ne_zero_of_mul_eq_one n₃
  have H1 : D.τ l₁ * D.τ l₂ * D.τ l₃ = 1 := by
    have := congrArg D.τ hd
    simpa only [map_mul, map_one] using this
  have c2 : D.τ l₁ * D.τ l₃ = l₂ := by
    linear_combination l₂ * H1 - D.τ l₁ * D.τ l₃ * n₂
  rw [D.tau_tau] at e3
  rw [c2] at e2
  have f1 : actK (t⁻¹ * h) (vXi D) = vXi D := by
    rw [actK_mul, h₁, map_smul, actK_inv_of_eigen hl₁ e1, smul_smul, mul_inv_cancel₀ hl₁,
      one_smul]
  have f2 : actK (t⁻¹ * h) (vE2 D) = vE2 D := by
    rw [actK_mul, h₂, map_smul, actK_inv_of_eigen hl₂ e2, smul_smul, mul_inv_cancel₀ hl₂,
      one_smul]
  have f3 : actK (t⁻¹ * h) (vE3 D) = vE3 D := by
    rw [actK_mul, h₃, map_smul, actK_inv_of_eigen hl₃ e3, smul_smul, mul_inv_cancel₀ hl₃,
      one_smul]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := fix_six_of_fix_frame D S.h2K f1 f2 f3
  have hsp : spinAction (quadOdd 3 (GaloisField p f)) (t⁻¹ * h) = 1 :=
    spinAction_eq_one_of_fix_six h2F _ a1 a2 a3 a4 a5 a6
  have hmem : t⁻¹ * h ∈ torusSub E := mem_torusSub_of_spinAction_eq_one S hsp
  have : h = t * (t⁻¹ * h) := by group
  rw [this]
  exact mul_mem ht hmem

end Main

end CFSG.ClassicalInvolution.PhanB3.S
