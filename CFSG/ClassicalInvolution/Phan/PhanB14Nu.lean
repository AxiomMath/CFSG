module

public import CFSG.ClassicalInvolution.Phan.PhanB13Quad
public import CFSG.ClassicalInvolution.Phan.Defs

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {F : Type} [Field F] [Algebra F K]

abbrev ent (A : Su K p f 2) (i j : Fin 2) : K :=
  ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j

theorem ent_mul (A B : Su K p f 2) (i j : Fin 2) :
    ent (A * B) i j = ent A i 0 * ent B 0 j + ent A i 1 * ent B 1 j := by
  show (((A : GL (Fin 2) K) * (B : GL (Fin 2) K) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j = _
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem ent_one_zero_zero : ent (1 : Su K p f 2) 0 0 = 1 := by simp [ent]
theorem ent_one_zero_one : ent (1 : Su K p f 2) 0 1 = 0 := by simp [ent]

theorem su_det (A : Su K p f 2) : ent A 0 0 * ent A 1 1 - ent A 0 1 * ent A 1 0 = 1 := by
  have := A.2.1
  rwa [Matrix.det_fin_two] at this

theorem su_entries (A : Su K p f 2) :
    ent A 1 1 = unitaryInvolution K p f (ent A 0 0) ∧
      ent A 1 0 = -unitaryInvolution K p f (ent A 0 1) := by
  set M : Matrix (Fin 2) (Fin 2) K := ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = 1 := A.2.1
  have hu : (M.map (unitaryInvolution K p f))ᵀ * M = 1 := A.2.2
  have h1 : M⁻¹ = (M.map (unitaryInvolution K p f))ᵀ := Matrix.inv_eq_left_inv hu
  have h2 : M⁻¹ = M.adjugate := by
    rw [Matrix.inv_def, hdet]
    simp
  have h3 := h2.symm.trans h1
  rw [Matrix.adjugate_fin_two] at h3
  have e00 := congrFun (congrFun h3 0) 0
  have e10 := congrFun (congrFun h3 1) 0
  simp at e00 e10
  refine ⟨?_, ?_⟩
  · exact e00
  · have : -M 1 0 = unitaryInvolution K p f (M 0 1) := by simpa using e10
    linear_combination -this

variable (Q : QData F K (unitaryInvolution K p f))

@[expose] def crd (A : Su K p f 2) : F × F × F × F :=
  (Q.re (ent A 0 0), Q.im (ent A 0 0), Q.re (ent A 0 1), Q.im (ent A 0 1))

theorem su_norm (A : Su K p f 2) :
    Q.re (ent A 0 0) * Q.re (ent A 0 0) + Q.im (ent A 0 0) * Q.im (ent A 0 0) +
      (Q.re (ent A 0 1) * Q.re (ent A 0 1) + Q.im (ent A 0 1) * Q.im (ent A 0 1)) = 1 := by
  obtain ⟨e11, e10⟩ := su_entries A
  have h := su_det A
  rw [e11, e10] at h
  have h' : ent A 0 0 * unitaryInvolution K p f (ent A 0 0) +
      ent A 0 1 * unitaryInvolution K p f (ent A 0 1) = 1 := by linear_combination h
  have := congrArg Q.re h'
  rwa [Q.re_add, Q.re_mul_σ, Q.re_mul_σ, Q.re_one] at this

theorem su_ext (A B : Su K p f 2) (h1 : Q.re (ent A 0 0) = Q.re (ent B 0 0))
    (h2 : Q.im (ent A 0 0) = Q.im (ent B 0 0)) (h3 : Q.re (ent A 0 1) = Q.re (ent B 0 1))
    (h4 : Q.im (ent A 0 1) = Q.im (ent B 0 1)) : A = B := by
  have ha : ent A 0 0 = ent B 0 0 := Q.re_inj h1 h2
  have hb : ent A 0 1 = ent B 0 1 := Q.re_inj h3 h4
  obtain ⟨a11, a10⟩ := su_entries A
  obtain ⟨b11, b10⟩ := su_entries B
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · show ent A 1 0 = ent B 1 0
    rw [a10, b10, hb]
  · show ent A 1 1 = ent B 1 1
    rw [a11, b11, ha]

theorem crd_mul_re_re (A B : Su K p f 2) :
    Q.re (ent (A * B) 0 0) = Q.re (ent A 0 0) * Q.re (ent B 0 0)
      - Q.im (ent A 0 0) * Q.im (ent B 0 0)
      - Q.re (ent A 0 1) * Q.re (ent B 0 1) - Q.im (ent A 0 1) * Q.im (ent B 0 1) := by
  obtain ⟨b11, b10⟩ := su_entries B
  rw [ent_mul, b10, Q.re_add, Q.re_mul, Q.re_mul, Q.re_neg, Q.im_neg, Q.re_σ, Q.im_σ]
  ring

theorem crd_mul_im_re (A B : Su K p f 2) :
    Q.im (ent (A * B) 0 0) = Q.re (ent A 0 0) * Q.im (ent B 0 0)
      + Q.im (ent A 0 0) * Q.re (ent B 0 0)
      + Q.re (ent A 0 1) * Q.im (ent B 0 1) - Q.im (ent A 0 1) * Q.re (ent B 0 1) := by
  obtain ⟨b11, b10⟩ := su_entries B
  rw [ent_mul, b10, Q.im_add, Q.im_mul, Q.im_mul, Q.re_neg, Q.im_neg, Q.re_σ, Q.im_σ]
  ring

theorem crd_mul_re_im (A B : Su K p f 2) :
    Q.re (ent (A * B) 0 1) = Q.re (ent A 0 0) * Q.re (ent B 0 1)
      - Q.im (ent A 0 0) * Q.im (ent B 0 1)
      + Q.re (ent A 0 1) * Q.re (ent B 0 0) + Q.im (ent A 0 1) * Q.im (ent B 0 0) := by
  obtain ⟨b11, b10⟩ := su_entries B
  rw [ent_mul, b11, Q.re_add, Q.re_mul, Q.re_mul, Q.re_σ, Q.im_σ]
  ring

theorem crd_mul_im_im (A B : Su K p f 2) :
    Q.im (ent (A * B) 0 1) = Q.re (ent A 0 0) * Q.im (ent B 0 1)
      + Q.im (ent A 0 0) * Q.re (ent B 0 1)
      - Q.re (ent A 0 1) * Q.im (ent B 0 0) + Q.im (ent A 0 1) * Q.re (ent B 0 0) := by
  obtain ⟨b11, b10⟩ := su_entries B
  rw [ent_mul, b11, Q.im_add, Q.im_mul, Q.im_mul, Q.re_σ, Q.im_σ]
  ring

end CFSG.ClassicalInvolution.PhanB3
