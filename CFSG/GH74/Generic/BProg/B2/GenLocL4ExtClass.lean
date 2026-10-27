module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtGen

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Matrix

namespace GenLocL4Ext

variable {F : Type} [Field F]

theorem i0_mul_xs_eq (c : F) :
    i0 c * xs = !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, -c; 0, 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [i0, xs, Matrix.mul_apply, Fin.sum_univ_four]

theorem four_class_std {c : F} (hc : ¬ IsSquare c) (h2 : (2 : F) ≠ 0) (g : Matrix (Fin 4) (Fin 4) F)
    (hgi : g * i0 c = i0 c * g) (hgx : g * xs = xs * g) {l : F} (hl : l ≠ 0)
    (hg2 : g * g = l • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∃ μ : F, μ ≠ 0 ∧ (g = μ • (1 : Matrix (Fin 4) (Fin 4) F) ∨ g = μ • xs ∨ g = μ • i0 c ∨
      g = μ • (i0 c * xs)) := by
  have hc0 : c ≠ 0 := fun h => hc ⟨0, by simp [h]⟩
  have half : ∀ x : F, -x = x → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination -hx
    exact (mul_eq_zero.1 this).resolve_left h2
  have half' : ∀ x : F, x = -x → x = 0 := fun x hx => half x hx.symm
  have x02 : g 0 2 = 0 := by
    have := congrFun (congrFun hgx 0) 2
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half _ this
  have x03 : g 0 3 = 0 := by
    have := congrFun (congrFun hgx 0) 3
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half _ this
  have x12 : g 1 2 = 0 := by
    have := congrFun (congrFun hgx 1) 2
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half _ this
  have x13 : g 1 3 = 0 := by
    have := congrFun (congrFun hgx 1) 3
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half _ this
  have x20 : g 2 0 = 0 := by
    have := congrFun (congrFun hgx 2) 0
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half' _ this
  have x21 : g 2 1 = 0 := by
    have := congrFun (congrFun hgx 2) 1
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half' _ this
  have x30 : g 3 0 = 0 := by
    have := congrFun (congrFun hgx 3) 0
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half' _ this
  have x31 : g 3 1 = 0 := by
    have := congrFun (congrFun hgx 3) 1
    simp [xs, Matrix.mul_apply, Fin.sum_univ_four] at this
    exact half' _ this
  have h01 : g 0 1 = c * g 1 0 := by
    simpa [i0, Matrix.mul_apply, Fin.sum_univ_four] using congrFun (congrFun hgi 0) 0
  have h11 : g 1 1 = g 0 0 := by
    simpa [i0, Matrix.mul_apply, Fin.sum_univ_four] using congrFun (congrFun hgi 1) 0
  have h23 : g 2 3 = c * g 3 2 := by
    simpa [i0, Matrix.mul_apply, Fin.sum_univ_four] using congrFun (congrFun hgi 2) 2
  have h33 : g 3 3 = g 2 2 := by
    simpa [i0, Matrix.mul_apply, Fin.sum_univ_four] using congrFun (congrFun hgi 3) 2
  obtain ⟨a, d, a', d', hg⟩ : ∃ a d a' d' : F, g = !![a, c * d, 0, 0; d, a, 0, 0; 0, 0, a', c * d';
      0, 0, d', a'] := by
    refine ⟨g 0 0, g 1 0, g 2 2, g 3 2, ?_⟩
    ext r k
    fin_cases r <;> fin_cases k <;> simp [h01, h11, h23, h33, x02, x03, x12, x13, x20, x21, x30, x31]
  subst hg
  have g00 := congrFun (congrFun hg2 0) 0
  have g10 := congrFun (congrFun hg2 1) 0
  have g22 := congrFun (congrFun hg2 2) 2
  have g32 := congrFun (congrFun hg2 3) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four] at g00 g10 g22 g32
  have had : a * d = 0 := by
    have : (2 : F) * (a * d) = 0 := by linear_combination g10
    exact (mul_eq_zero.1 this).resolve_left h2
  have had' : a' * d' = 0 := by
    have : (2 : F) * (a' * d') = 0 := by linear_combination g32
    exact (mul_eq_zero.1 this).resolve_left h2
  clear hgi hgx hg2 x02 x03 x12 x13 x20 x21 x30 x31 h01 h11 h23 h33 g10 g32
  rcases mul_eq_zero.1 had with ha | hd
  · subst ha
    rcases mul_eq_zero.1 had' with ha' | hd'
    · subst ha'
      have hd0 : d ≠ 0 := fun h => hl (by rw [← g00, h]; ring)
      have hsq : d * d = d' * d' := by
        have h3 : c * (d * d - d' * d') = 0 := by linear_combination g00 - g22
        have h4 := (mul_eq_zero.1 h3).resolve_left hc0
        linear_combination h4
      rcases mul_self_eq_mul_self_iff.1 hsq with h | h
      · refine ⟨d, hd0, Or.inr (Or.inr (Or.inl ?_))⟩
        subst h
        ext r k
        fin_cases r <;> fin_cases k <;> simp [i0, mul_comm]
      · refine ⟨d, hd0, Or.inr (Or.inr (Or.inr ?_))⟩
        have h5 : d' = -d := by linear_combination h
        subst h5
        rw [i0_mul_xs_eq]
        ext r k
        fin_cases r <;> fin_cases k <;> simp [mul_comm]
    · subst hd'
      exfalso
      have hd0 : d ≠ 0 := fun h => hl (by rw [← g00, h]; ring)
      apply hc
      refine ⟨a' / d, ?_⟩
      field_simp
      linear_combination g00 - g22
  · subst hd
    rcases mul_eq_zero.1 had' with ha' | hd'
    · subst ha'
      exfalso
      have hd0' : d' ≠ 0 := fun h => hl (by rw [← g22, h]; ring)
      apply hc
      refine ⟨a / d', ?_⟩
      field_simp
      linear_combination g22 - g00
    · subst hd'
      have ha0 : a ≠ 0 := fun h => hl (by rw [← g00, h]; ring)
      have hsq : a * a = a' * a' := by linear_combination g00 - g22
      rcases mul_self_eq_mul_self_iff.1 hsq with h | h
      · refine ⟨a, ha0, Or.inl ?_⟩
        subst h
        ext r k
        fin_cases r <;> fin_cases k <;> simp
      · refine ⟨a, ha0, Or.inr (Or.inl ?_)⟩
        have h5 : a' = -a := by linear_combination h
        subst h5
        ext r k
        fin_cases r <;> fin_cases k <;> simp [xs]

theorem conj_inv_mul_conj (B : GL (Fin 4) F) (X Y : Matrix (Fin 4) (Fin 4) F) :
    (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X * (B : Matrix (Fin 4) (Fin 4) F)) *
        (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Y * (B : Matrix (Fin 4) (Fin 4) F)) =
      ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X * Y) * (B : Matrix (Fin 4) (Fin 4) F) := by
  simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem four_class {c : F} (hc : ¬ IsSquare c) (h2 : (2 : F) ≠ 0) (B : GL (Fin 4) F)
    (i N : Matrix (Fin 4) (Fin 4) F) {s : F} (hs : s ≠ 0)
    (hi : i * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * i0 c)
    (hN : (s⁻¹ • N) * (B : Matrix (Fin 4) (Fin 4) F) = (B : Matrix (Fin 4) (Fin 4) F) * xs)
    (g : Matrix (Fin 4) (Fin 4) F) (hgi : g * i = i * g) (hgN : g * N = N * g) {l : F} (hl : l ≠ 0)
    (hg2 : g * g = l • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∃ μ : F, μ ≠ 0 ∧ (g = μ • (1 : Matrix (Fin 4) (Fin 4) F) ∨ g = μ • N ∨ g = μ • i ∨
      g = μ • (i * N)) := by
  set B' : Matrix (Fin 4) (Fin 4) F := ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hB'
  have hBB : (B : Matrix (Fin 4) (Fin 4) F) * B' = 1 := B.mul_inv
  have hI0 : i0 c = B' * i * (B : Matrix (Fin 4) (Fin 4) F) := by
    rw [Matrix.mul_assoc, hi, ← Matrix.mul_assoc, hB', Units.inv_mul, Matrix.one_mul]
  have hxs : xs = B' * (s⁻¹ • N) * (B : Matrix (Fin 4) (Fin 4) F) := by
    rw [Matrix.mul_assoc, hN, ← Matrix.mul_assoc, hB', Units.inv_mul, Matrix.one_mul]
  have hi' : i = (B : Matrix (Fin 4) (Fin 4) F) * i0 c * B' := by
    rw [← hi, hB', Units.mul_inv_cancel_right]
  have hN' : s⁻¹ • N = (B : Matrix (Fin 4) (Fin 4) F) * xs * B' := by
    rw [← hN, hB', Units.mul_inv_cancel_right]
  set g' : Matrix (Fin 4) (Fin 4) F := B' * g * (B : Matrix (Fin 4) (Fin 4) F) with hg'
  have hgg' : g = (B : Matrix (Fin 4) (Fin 4) F) * g' * B' := by
    rw [hg', hB']
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv_cancel_right]
  have e1 : g' * i0 c = i0 c * g' := by
    rw [hI0, hg', hB', conj_inv_mul_conj, conj_inv_mul_conj, hgi]
  have hxs' : xs = s⁻¹ • (B' * N * (B : Matrix (Fin 4) (Fin 4) F)) := by
    rw [hxs, Matrix.mul_smul, Matrix.smul_mul]
  have e2 : g' * xs = xs * g' := by
    have e3 : g' * (B' * N * (B : Matrix (Fin 4) (Fin 4) F)) =
        (B' * N * (B : Matrix (Fin 4) (Fin 4) F)) * g' := by
      rw [hg', hB', conj_inv_mul_conj, conj_inv_mul_conj, hgN]
    rw [hxs', Matrix.mul_smul, Matrix.smul_mul, e3]
  have e4 : g' * g' = l • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [hg', hB', conj_inv_mul_conj, hg2]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]
  obtain ⟨μ, hμ, h | h | h | h⟩ := four_class_std hc h2 g' e1 e2 hl e4
  · refine ⟨μ, hμ, Or.inl ?_⟩
    rw [hgg', h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hBB]
  · refine ⟨μ * s⁻¹, mul_ne_zero hμ (inv_ne_zero hs), Or.inr (Or.inl ?_)⟩
    rw [hgg', h, Matrix.mul_smul, Matrix.smul_mul, ← hN', smul_smul]
  · refine ⟨μ, hμ, Or.inr (Or.inr (Or.inl ?_))⟩
    rw [hgg', h, Matrix.mul_smul, Matrix.smul_mul, ← hi']
  · refine ⟨μ * s⁻¹, mul_ne_zero hμ (inv_ne_zero hs), Or.inr (Or.inr (Or.inr ?_))⟩
    have e5 : (B : Matrix (Fin 4) (Fin 4) F) * (i0 c * xs) * B' = i * (s⁻¹ • N) := by
      rw [← conj_mul_conj, ← hi', ← hN']
    rw [hgg', h, Matrix.mul_smul, Matrix.smul_mul, e5, Matrix.mul_smul, smul_smul]

end GenLocL4Ext

end CFSG.GH74.Generic.BProg.B2
