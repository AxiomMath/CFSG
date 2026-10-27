module

public import CFSG.ClassicalInvolution.ModelFacts.LinearAutBlock

public section

namespace CFSG.ClassicalInvolution.Asc77.C5P

open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def upT (t : F) : SL(2, F) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem conj_upT_sq (t : F) {s : F} (hs : s ≠ 0) :
    ∃ g : SL(2, F), g * upT t * g⁻¹ = upT (s ^ 2 * t) := by
  refine ⟨⟨!![s, 0; 0, s⁻¹], by simp [Matrix.det_fin_two, hs]⟩, ?_⟩
  apply Subtype.ext
  show (!![s, 0; 0, s⁻¹] : Matrix (Fin 2) (Fin 2) F) * !![1, t; 0, 1] *
      Matrix.adjugate !![s, 0; 0, s⁻¹] = !![1, s ^ 2 * t; 0, 1]
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs]
  ring

theorem exists_conj_upT (h2 : (2 : F) ≠ 0) (u : SL(2, F))
    (htr : Matrix.trace (u : Matrix (Fin 2) (Fin 2) F) = 2) (hu : u ≠ 1) :
    ∃ g : SL(2, F), ∃ t : F, t ≠ 0 ∧ g * u * g⁻¹ = upT t := by
  set a := (u : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (u : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (u : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (u : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hu' : (u : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] := Matrix.eta_fin_two _
  have hdet : a * d - b * c = 1 := by
    have := u.2
    rw [Matrix.det_fin_two] at this
    exact this
  have htr' : a + d = 2 := by
    rw [Matrix.trace_fin_two] at htr
    exact htr
  by_cases hb0 : b = 0
  ·
    have had : a * d = 1 := by rw [hb0] at hdet; simpa using hdet
    have ha1 : a = 1 := by
      have h1 : (a - 1) ^ 2 = 0 := by linear_combination (-1 : F) * had + a * htr'
      exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h1)
    have hd1 : d = 1 := by linear_combination htr' - ha1
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hu
      apply Subtype.ext
      rw [hu', ha1, hd1, hb0, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    refine ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, -c, neg_ne_zero.mpr hc0, ?_⟩
    apply Subtype.ext
    show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) *
        Matrix.adjugate !![0, 1; -1, 0] = !![1, -c; 0, 1]
    rw [Matrix.adjugate_fin_two, hu', ha1, hd1, hb0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ·
    set y := (a - d) / (2 * b) with hy
    have hyb : y * b = (a - d) / 2 := by
      rw [hy]; field_simp
    have key : 4 * b * c + (a - d) ^ 2 = 0 := by
      linear_combination (-4 : F) * hdet + (a + d + 2) * htr'
    have e1 : a - y * b = 1 := by
      rw [hyb]; field_simp; linear_combination htr'
    have e2 : y * b + d = 1 := by
      rw [hyb]; field_simp; linear_combination htr'
    have e3 : c + y * (a - d) - y * (y * b) = 0 := by
      have h2by : 2 * b * y = a - d := by rw [hy]; field_simp
      have h4b : 4 * b ≠ 0 := mul_ne_zero (by
        have : (4 : F) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2) hb0
      have hmul : 4 * b * (c + y * (a - d) - y * (y * b)) = 0 := by
        linear_combination key - (2 * b * y - (a - d)) * h2by
      exact (mul_eq_zero.mp hmul).resolve_left h4b
    refine ⟨⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two]⟩, b, hb0, ?_⟩
    apply Subtype.ext
    show (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) F) * (u : Matrix (Fin 2) (Fin 2) F) *
        Matrix.adjugate !![1, 0; y, 1] = !![1, b; 0, 1]
    have hprod : (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) F) * !![a, b; c, d] *
        !![1, -0; -y, 1] = !![a - y * b, b; c + y * (a - d) - y * (y * b), y * b + d] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    rw [Matrix.adjugate_fin_two_of, hu', hprod, e1, e2, e3]

theorem isSquare_mul_of_not [Finite F] {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hx' : ¬ IsSquare x) (hy' : ¬ IsSquare y) : IsSquare (x * y) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h1 := quadraticChar_neg_one_iff_not_isSquare.mpr hx'
  have h2 := quadraticChar_neg_one_iff_not_isSquare.mpr hy'
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hx hy), map_mul, h1, h2]
  norm_num

theorem conj_of_sq {u v g h : SL(2, F)} {t t' : F} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (hu : g * u * g⁻¹ = upT t) (hv : h * v * h⁻¹ = upT t') (hsq : IsSquare (t' / t)) :
    ∃ k : SL(2, F), v = k * u * k⁻¹ := by
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact div_ne_zero ht' ht hs
  have ht'' : t' = s ^ 2 * t := by
    rw [div_eq_iff ht] at hs
    rw [sq]; exact hs
  obtain ⟨m, hm⟩ := conj_upT_sq t hs0
  refine ⟨h⁻¹ * m * g, ?_⟩
  calc v = h⁻¹ * (h * v * h⁻¹) * h := by group
    _ = h⁻¹ * (m * upT t * m⁻¹) * h := by rw [hv, ht'', ← hm]
    _ = h⁻¹ * (m * (g * u * g⁻¹) * m⁻¹) * h := by rw [hu]
    _ = h⁻¹ * m * g * u * (h⁻¹ * m * g)⁻¹ := by group

theorem trace_eq_two_of_orderOf [Finite F] {u : SL(2, F)} (hu : orderOf u = ringChar F) :
    Matrix.trace (u : Matrix (Fin 2) (Fin 2) F) = 2 := by
  have h := CFSG.ClassicalInvolution.ModelFacts.LinearAut.trace_sub_one_of_pow_eq_one
    (n := 2) (by norm_num) (hu ▸ pow_orderOf_eq_one u)
  rw [Matrix.trace_sub, Matrix.trace_one] at h
  simpa [sub_eq_zero] using h

theorem sl2_two_classes [Finite F] (h2 : (2 : F) ≠ 0) {u v w : SL(2, F)}
    (hu : orderOf u = ringChar F) (hv : orderOf v = ringChar F)
    (hw : orderOf w = ringChar F) :
    (∃ g, v = g * u * g⁻¹) ∨ (∃ g, w = g * u * g⁻¹) ∨ (∃ g, w = g * v * g⁻¹) := by
  have hne : ∀ x : SL(2, F), orderOf x = ringChar F → x ≠ 1 := by
    intro x hx h1
    rw [h1, orderOf_one] at hx
    exact (CharP.char_is_prime F (ringChar F)).one_lt.ne hx
  obtain ⟨gu, tu, htu, hgu⟩ := exists_conj_upT h2 u (trace_eq_two_of_orderOf hu) (hne u hu)
  obtain ⟨gv, tv, htv, hgv⟩ := exists_conj_upT h2 v (trace_eq_two_of_orderOf hv) (hne v hv)
  obtain ⟨gw, tw, htw, hgw⟩ := exists_conj_upT h2 w (trace_eq_two_of_orderOf hw) (hne w hw)
  by_cases h1 : IsSquare (tv / tu)
  · exact Or.inl (conj_of_sq htu htv hgu hgv h1)
  by_cases h3 : IsSquare (tw / tv)
  · exact Or.inr (Or.inr (conj_of_sq htv htw hgv hgw h3))
  refine Or.inr (Or.inl (conj_of_sq htu htw hgu hgw ?_))
  have := isSquare_mul_of_not (div_ne_zero htw htv) (div_ne_zero htv htu) h3 h1
  rwa [div_mul_div_cancel₀ htv] at this

end CFSG.ClassicalInvolution.Asc77.C5P
