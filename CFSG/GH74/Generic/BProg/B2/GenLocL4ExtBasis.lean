module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Matrix

namespace GenLocL4Ext

variable {F : Type} [Field F]

theorem exists_ne_zero_mulVec {M : Matrix (Fin 4) (Fin 4) F} (hM : M ≠ 0) :
    ∃ u : Fin 4 → F, M *ᵥ u ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [h, Matrix.zero_mulVec]

theorem zero_of_comb {c : F} (hc : ¬ IsSquare c) {i : Matrix (Fin 4) (Fin 4) F}
    (hi : i * i = c • (1 : Matrix (Fin 4) (Fin 4) F)) {v : Fin 4 → F} (hv : v ≠ 0) {a b : F}
    (h : a • v + b • (i *ᵥ v) = 0) : a = 0 ∧ b = 0 := by
  have h2 : i *ᵥ (a • v + b • (i *ᵥ v)) = 0 := by rw [h, Matrix.mulVec_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hi,
    Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  have h3 : (a * a - c * (b * b)) • v = 0 := by
    linear_combination (norm := module) a • h - b • h2
  have h4 : a * a - c * (b * b) = 0 := (smul_eq_zero.1 h3).resolve_right hv
  have hb : b = 0 := by
    by_contra hb
    apply hc
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination (-1 : F) * h4
  subst hb
  refine ⟨?_, rfl⟩
  have : a * a = 0 := by simpa using h4
  exact mul_self_eq_zero.1 this

@[expose] def colMat (i : Matrix (Fin 4) (Fin 4) F) (v w : Fin 4 → F) : Matrix (Fin 4) (Fin 4) F :=
  Matrix.of fun r k => (![v, i *ᵥ v, w, i *ᵥ w] : Fin 4 → (Fin 4 → F)) k r

theorem colMat_mulVec (i : Matrix (Fin 4) (Fin 4) F) (v w y : Fin 4 → F) :
    colMat i v w *ᵥ y = y 0 • v + y 1 • (i *ᵥ v) + y 2 • w + y 3 • (i *ᵥ w) := by
  ext r
  simp [colMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem colMat_col (i : Matrix (Fin 4) (Fin 4) F) (v w : Fin 4 → F) (k : Fin 4) :
    (colMat i v w).col k = ![v, i *ᵥ v, w, i *ᵥ w] k := by
  ext r
  simp [colMat, Matrix.col]

theorem colMat_i0 (c : F) (i : Matrix (Fin 4) (Fin 4) F)
    (hi : i * i = c • (1 : Matrix (Fin 4) (Fin 4) F)) (v w : Fin 4 → F) :
    i * colMat i v w = colMat i v w * i0 c := by
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  fin_cases k
  all_goals
    simp [colMat_mulVec, colMat_col, i0, hi, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem colMat_N (i N : Matrix (Fin 4) (Fin 4) F) (s : F) (hiN : i * N = N * i) (v w : Fin 4 → F)
    (hv : N *ᵥ v = s • v) (hw : N *ᵥ w = (-s) • w) :
    N * colMat i v w = colMat i v w * (s • xs) := by
  have hiv : N *ᵥ (i *ᵥ v) = s • (i *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← hiN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hiw : N *ᵥ (i *ᵥ w) = (-s) • (i *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, ← hiN, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  fin_cases k
  all_goals simp [colMat_mulVec, colMat_col, xs, hv, hw, hiv, hiw]

theorem colMat_isUnit {c : F} (hc : ¬ IsSquare c) (h2 : (2 : F) ≠ 0)
    (i N : Matrix (Fin 4) (Fin 4) F) {s : F} (hs : s ≠ 0)
    (hi : i * i = c • (1 : Matrix (Fin 4) (Fin 4) F)) (hiN : i * N = N * i) {v w : Fin 4 → F}
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hv : N *ᵥ v = s • v) (hw : N *ᵥ w = (-s) • w) :
    IsUnit (colMat i v w) := by
  have hiv : N *ᵥ (i *ᵥ v) = s • (i *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← hiN, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hiw : N *ᵥ (i *ᵥ w) = (-s) • (i *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, ← hiN, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have key : ∀ y : Fin 4 → F, colMat i v w *ᵥ y = 0 → y = 0 := by
    intro y hy
    rw [colMat_mulVec] at hy
    have h1 : (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ
        (y 0 • v + y 1 • (i *ᵥ v) + y 2 • w + y 3 • (i *ᵥ w)) = 0 := by
      rw [hy, Matrix.mulVec_zero]
    have e1 : (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ v = (2 * s) • v := by
      rw [Matrix.add_mulVec, hv, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e2 : (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ (i *ᵥ v) = (2 * s) • (i *ᵥ v) := by
      rw [Matrix.add_mulVec, hiv, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e3 : (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ w = 0 := by
      rw [Matrix.add_mulVec, hw, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    have e4 : (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ (i *ᵥ w) = 0 := by
      rw [Matrix.add_mulVec, hiw, Matrix.smul_mulVec, Matrix.one_mulVec]; module
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, e1, e2, e3, e4] at h1
    have h3 : (2 * s) • (y 0 • v + y 1 • (i *ᵥ v)) = 0 := by
      linear_combination (norm := module) h1
    have h4 : y 0 • v + y 1 • (i *ᵥ v) = 0 := (smul_eq_zero.1 h3).resolve_left (mul_ne_zero h2 hs)
    obtain ⟨hy0, hy1⟩ := zero_of_comb hc hi hv0 h4
    rw [hy0, hy1] at hy
    have h5 : y 2 • w + y 3 • (i *ᵥ w) = 0 := by
      linear_combination (norm := module) hy
    obtain ⟨hy2, hy3⟩ := zero_of_comb hc hi hw0 h5
    funext k
    fin_cases k <;> simp [hy0, hy1, hy2, hy3]
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro y z hyz
  have := key (y - z) (by rw [Matrix.mulVec_sub, hyz, sub_self])
  exact sub_eq_zero.1 this

theorem exists_split_basis {c : F} (hc : ¬ IsSquare c) (h2 : (2 : F) ≠ 0)
    (i N : Matrix (Fin 4) (Fin 4) F) {s : F} (hs : s ≠ 0)
    (hi : i * i = c • (1 : Matrix (Fin 4) (Fin 4) F))
    (hN : N * N = (s * s) • (1 : Matrix (Fin 4) (Fin 4) F)) (hiN : i * N = N * i)
    (hN1 : N ≠ s • (1 : Matrix (Fin 4) (Fin 4) F)) (hN2 : N ≠ -(s • (1 : Matrix (Fin 4) (Fin 4) F))) :
    ∃ B : GL (Fin 4) F, i * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * i0 c ∧
      (s⁻¹ • N) * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * xs := by
  obtain ⟨u, hu⟩ := exists_ne_zero_mulVec (M := N + s • (1 : Matrix (Fin 4) (Fin 4) F))
    (fun h => hN2 (eq_neg_of_add_eq_zero_left h))
  obtain ⟨u', hu'⟩ := exists_ne_zero_mulVec (M := N - s • (1 : Matrix (Fin 4) (Fin 4) F))
    (fun h => hN1 (sub_eq_zero.1 h))
  have hNp : N * (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) =
      s • (N + s • (1 : Matrix (Fin 4) (Fin 4) F)) := by
    rw [mul_add, hN, mul_smul_comm, mul_one, smul_add, smul_smul, add_comm]
  have hNm : N * (N - s • (1 : Matrix (Fin 4) (Fin 4) F)) =
      (-s) • (N - s • (1 : Matrix (Fin 4) (Fin 4) F)) := by
    rw [mul_sub, hN, mul_smul_comm, mul_one, smul_sub, smul_smul, neg_smul, neg_mul, neg_smul]
    abel
  have hv : N *ᵥ ((N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ u) =
      s • ((N + s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, hNp, Matrix.smul_mulVec]
  have hw : N *ᵥ ((N - s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ u') =
      (-s) • ((N - s • (1 : Matrix (Fin 4) (Fin 4) F)) *ᵥ u') := by
    rw [Matrix.mulVec_mulVec, hNm, Matrix.smul_mulVec]
  have hunit := colMat_isUnit hc h2 i N hs hi hiN hu hu' hv hw
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact colMat_i0 c i hi _ _
  · rw [IsUnit.unit_spec, smul_mul_assoc, colMat_N i N s hiN _ _ hv hw, mul_smul_comm, smul_smul,
      inv_mul_cancel₀ hs, one_smul]

end GenLocL4Ext

end CFSG.GH74.Generic.BProg.B2
