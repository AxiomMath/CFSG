module

public import CFSG.ClassicalInvolution.Phan.PhanB15Hom

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] [Algebra F K]

theorem exists_su (hK : Nat.card K = (p ^ f) ^ 2) {a b : K}
    (h : a * unitaryInvolution K p f a + b * unitaryInvolution K p f b = 1) :
    ∃ A : Su K p f 2, ent A 0 0 = a ∧ ent A 0 1 = b := by
  set σ := unitaryInvolution K p f with hσ
  have hinv : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  let M : Matrix (Fin 2) (Fin 2) K := !![a, b; -σ b, σ a]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    linear_combination h
  let g : SL(2, K) := ⟨M, hdet⟩
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL g, ?_, ?_⟩, ?_, ?_⟩
  · simp
  · show conjTr σ M * M = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [conjTr, M, Matrix.mul_apply, Fin.sum_univ_two, hinv]
    · linear_combination h
    · ring
    · ring
    · linear_combination h
  · rfl
  · rfl

variable (Q : QData F K (unitaryInvolution K p f)) (c d : F)

theorem nuQ_injective (hcd : c * c + d * d = -1) (h2 : (2 : F) ≠ 0) :
    Function.Injective (nuQ Q c d hcd) := by
  intro A B hAB
  have h := congrArg (fun X : SL(2, F) => (X : Matrix (Fin 2) (Fin 2) F)) hAB
  simp only [coe_nuQ, nuOf, nuMat] at h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  have ha1 : Q.re (ent A 0 0) = Q.re (ent B 0 0) := by
    apply mul_left_cancel₀ h2
    linear_combination e00 + e11
  have ha2 : Q.im (ent A 0 0) = Q.im (ent B 0 0) := by
    apply mul_left_cancel₀ h2
    linear_combination e10 - e01
  have u1 : (Q.re (ent A 0 1) - Q.re (ent B 0 1)) * c - (Q.im (ent A 0 1) - Q.im (ent B 0 1)) * d
      = 0 := by
    apply mul_left_cancel₀ h2
    linear_combination e00 - e11
  have v1 : (Q.re (ent A 0 1) - Q.re (ent B 0 1)) * d + (Q.im (ent A 0 1) - Q.im (ent B 0 1)) * c
      = 0 := by
    apply mul_left_cancel₀ h2
    linear_combination e10 + e01
  have hu : Q.re (ent A 0 1) - Q.re (ent B 0 1) = 0 := by
    linear_combination (-(c)) * u1 - d * v1 + (Q.re (ent A 0 1) - Q.re (ent B 0 1)) * hcd
  have hv : Q.im (ent A 0 1) - Q.im (ent B 0 1) = 0 := by
    rw [hu] at u1 v1
    have : (Q.im (ent A 0 1) - Q.im (ent B 0 1)) * (c * c + d * d) = 0 := by
      linear_combination (-(d)) * u1 + c * v1
    rw [hcd] at this
    linear_combination -this
  exact su_ext Q A B ha1 ha2 (sub_eq_zero.mp hu) (sub_eq_zero.mp hv)

theorem exists_su_of_entries (hK : Nat.card K = (p ^ f) ^ 2) (hcd : c * c + d * d = -1)
    (h2 : (2 : F) ≠ 0) (m11 m12 m21 m22 : F) (hdet : m11 * m22 - m12 * m21 = 1) :
    ∃ A : Su K p f 2, nuOf Q c d A = !![m11, m12; m21, m22] := by
  set u : F := (m11 - m22) / 2 with hu
  set v : F := (m12 + m21) / 2 with hv
  set α₁ : F := (m11 + m22) / 2 with hα₁
  set α₂ : F := (m21 - m12) / 2 with hα₂
  set β₁ : F := -(c * u + d * v) with hβ₁
  set β₂ : F := -(c * v - d * u) with hβ₂
  have hsum : α₁ * α₁ + α₂ * α₂ + (β₁ * β₁ + β₂ * β₂) = 1 := by
    rw [hα₁, hα₂, hβ₁, hβ₂, hu, hv]
    field_simp
    linear_combination ((m11 - m22) ^ 2 + (m12 + m21) ^ 2) * hcd + 4 * hdet
  set a : K := Q.cpl α₁ α₂ with ha
  set b : K := Q.cpl β₁ β₂ with hb
  have hnorm : a * unitaryInvolution K p f a + b * unitaryInvolution K p f b = 1 := by
    apply Q.re_inj
    · rw [Q.re_add, Q.re_mul_σ, Q.re_mul_σ, Q.re_one, ha, hb, Q.re_cpl, Q.im_cpl, Q.re_cpl,
        Q.im_cpl]
      linear_combination hsum
    · rw [Q.im_add, Q.im_mul_σ, Q.im_mul_σ, Q.im_one]
      ring
  obtain ⟨A, hA0, hA1⟩ := exists_su hK hnorm
  refine ⟨A, ?_⟩
  rw [nuOf, hA0, hA1, ha, hb, Q.re_cpl, Q.im_cpl, Q.re_cpl, Q.im_cpl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [nuMat, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · rw [hα₁, hβ₁, hβ₂, hu, hv]
    field_simp
    linear_combination (-(m11 - m22)) * hcd
  · rw [hα₂, hβ₁, hβ₂, hu, hv]
    field_simp
    linear_combination (-(m12 + m21)) * hcd
  · rw [hα₂, hβ₁, hβ₂, hu, hv]
    field_simp
    linear_combination (-(m12 + m21)) * hcd
  · rw [hα₁, hβ₁, hβ₂, hu, hv]
    field_simp
    linear_combination ((m11 - m22)) * hcd

theorem nuQ_surjective (hK : Nat.card K = (p ^ f) ^ 2) (hcd : c * c + d * d = -1)
    (h2 : (2 : F) ≠ 0) : Function.Surjective (nuQ Q c d hcd) := by
  intro M
  have hdet : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  obtain ⟨A, hA⟩ := exists_su_of_entries Q c d hK hcd h2 _ _ _ _ hdet
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_nuQ, hA]
  exact (Matrix.eta_fin_two _).symm

end CFSG.ClassicalInvolution.PhanB3
