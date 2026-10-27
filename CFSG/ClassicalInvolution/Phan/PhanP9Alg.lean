module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Reflection

public section

namespace CFSG.ClassicalInvolution.PhanP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs Matrix
open scoped MatrixGroups

section Algebra

variable {F : Type} [Field F]

theorem reflM_reflM_apply {v w : Matrix (Fin 2) (Fin 2) F} (hv : v.det ≠ 0) (hw : w.det ≠ 0)
    (X : Matrix (Fin 2) (Fin 2) F) :
    reflM v (reflM w X) = ((v.det * w.det)⁻¹) • (v * adjugate w * X * adjugate w * v) := by
  obtain ⟨p, q, r, s, rfl⟩ := exists_eq_of_fin_two v
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_of_fin_two w
  obtain ⟨x, y, z, t, rfl⟩ := exists_eq_of_fin_two X
  simp only [Matrix.det_fin_two_of] at hv hw
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflM, polarDet, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of] <;> field_simp <;>
      ring

@[expose] def reflWord : List (Matrix (Fin 2) (Fin 2) F) → Matrix (Fin 2) (Fin 2) F →
    Matrix (Fin 2) (Fin 2) F
  | [], X => X
  | v :: vs, X => reflM v (reflWord vs X)

@[expose] def detProd (vs : List (Matrix (Fin 2) (Fin 2) F)) : F := (vs.map Matrix.det).prod

theorem detProd_cons (v : Matrix (Fin 2) (Fin 2) F) (vs : List (Matrix (Fin 2) (Fin 2) F)) :
    detProd (v :: vs) = v.det * detProd vs := by
  simp [detProd]

theorem exists_LR_of_even : ∀ (n : ℕ) (vs : List (Matrix (Fin 2) (Fin 2) F)),
    vs.length = 2 * n → (∀ v ∈ vs, v.det ≠ 0) →
      ∃ A B : Matrix (Fin 2) (Fin 2) F, A.det = detProd vs ∧ B.det = detProd vs ∧
        ∀ X, reflWord vs X = (detProd vs)⁻¹ • (A * X * B)
  | 0, vs, hlen, _ => by
    have : vs = [] := List.length_eq_zero_iff.1 (by simpa using hlen)
    subst this
    refine ⟨1, 1, by simp [detProd], by simp [detProd], fun X => ?_⟩
    simp [reflWord, detProd]
  | n + 1, vs, hlen, hdet => by
    match vs, hlen with
    | v :: w :: vs', hlen =>
      have hv : v.det ≠ 0 := hdet v (by simp)
      have hw : w.det ≠ 0 := hdet w (by simp)
      have hlen' : vs'.length = 2 * n := by simp at hlen; omega
      obtain ⟨A', B', hA', hB', hX'⟩ := exists_LR_of_even n vs' hlen'
        (fun u hu => hdet u (by simp [hu]))
      refine ⟨v * adjugate w * A', B' * adjugate w * v, ?_, ?_, fun X => ?_⟩
      · rw [detProd_cons, detProd_cons, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate, hA']
        simp only [Fintype.card_fin]
        ring
      · rw [detProd_cons, detProd_cons, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate, hB']
        simp only [Fintype.card_fin]
        ring
      · simp only [reflWord]
        rw [hX', reflM_reflM_apply hv hw, detProd_cons, detProd_cons, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.smul_mul, smul_smul]
        have e1 : (v.det * w.det)⁻¹ * (detProd vs')⁻¹ = (v.det * (w.det * detProd vs'))⁻¹ := by
          rw [← mul_inv]
          ring_nf
        rw [e1]
        congr 1
        simp only [Matrix.mul_assoc]

theorem detProd_ne_zero (vs : List (Matrix (Fin 2) (Fin 2) F)) (h : ∀ v ∈ vs, v.det ≠ 0) :
    detProd vs ≠ 0 := by
  induction vs with
  | nil => simp [detProd]
  | cons v vs ih =>
    rw [detProd_cons]
    exact mul_ne_zero (h v (by simp)) (ih fun u hu => h u (by simp [hu]))

theorem exists_SL_of_even (n : ℕ) (vs : List (Matrix (Fin 2) (Fin 2) F)) (hlen : vs.length = 2 * n)
    (hdet : ∀ v ∈ vs, v.det ≠ 0) {c : F} (hc : detProd vs = c * c) :
    ∃ A B : SL(2, F), ∀ X, reflWord vs X = (A : Matrix (Fin 2) (Fin 2) F) * X * B := by
  obtain ⟨A, B, hA, hB, hX⟩ := exists_LR_of_even n vs hlen hdet
  have hD := detProd_ne_zero vs hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hD (by rw [hc]; ring)
  have hA1 : (c⁻¹ • A).det = 1 := by
    rw [Matrix.det_smul, hA, hc]
    simp only [Fintype.card_fin]
    field_simp
  have hB1 : (c⁻¹ • B).det = 1 := by
    rw [Matrix.det_smul, hB, hc]
    simp only [Fintype.card_fin]
    field_simp
  refine ⟨⟨c⁻¹ • A, hA1⟩, ⟨c⁻¹ • B, hB1⟩, fun X => ?_⟩
  rw [hX, hc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rw [← mul_inv]

end Algebra

end CFSG.ClassicalInvolution.PhanP
