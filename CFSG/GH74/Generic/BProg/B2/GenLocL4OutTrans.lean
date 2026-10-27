module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutAbs2
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutSplit

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section Transport

variable {F : Type} [Field F]

theorem eq_iff_conj {Pm Pi X Y : Matrix (Fin 4) (Fin 4) F} (hPP : Pm * Pi = 1) :
    X = Y ↔ Pi * X * Pm = Pi * Y * Pm := by
  have e1 : ∀ W : Matrix (Fin 4) (Fin 4) F, Pm * (Pi * W * Pm) * Pi = W := fun W => by
    calc Pm * (Pi * W * Pm) * Pi = (Pm * Pi) * W * (Pm * Pi) := by simp only [Matrix.mul_assoc]
      _ = W := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  constructor
  · intro h
    rw [h]
  · intro h
    rw [← e1 X, h, e1 Y]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem conj_commute_iff (P : GL (Fin 4) F) (z : SL(4, F)) (M : Matrix (Fin 4) (Fin 4) F) :
    ((((slConjugation 4 F P).toMonoidHom z : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * M =
      M * (((slConjugation 4 F P).toMonoidHom z : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) ↔
    ((z : Matrix (Fin 4) (Fin 4) F) * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M * (P : Matrix (Fin 4) (Fin 4) F)) =
      (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * M * (P : Matrix (Fin 4) (Fin 4) F)) * (z : Matrix (Fin 4) (Fin 4) F)) := by
  rw [coe_conj]
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  refine (eq_iff_conj hPP).trans ?_
  have l1 : Pi * (Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi * M) * Pm = (z : Matrix (Fin 4) (Fin 4) F) * (Pi * M * Pm) := by
    calc Pi * (Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi * M) * Pm
        = (Pi * Pm) * (z : Matrix (Fin 4) (Fin 4) F) * (Pi * M * Pm) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, Matrix.one_mul]
  have l2 : Pi * (M * (Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi)) * Pm = (Pi * M * Pm) * (z : Matrix (Fin 4) (Fin 4) F) := by
    calc Pi * (M * (Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi)) * Pm
        = (Pi * M * Pm) * (z : Matrix (Fin 4) (Fin 4) F) * (Pi * Pm) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, Matrix.mul_one]
  rw [l1, l2]

theorem conj_form_aux {Pm Pi X N : Matrix (Fin 4) (Fin 4) F} (hPP : Pm * Pi = 1) (hPiP : Pi * Pm = 1) :
    Pm * X * Pmᵀ = N ↔ X = Pi * N * Piᵀ := by
  have hPt : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have hPt' : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  constructor
  · intro h
    rw [← h]
    calc X = (Pi * Pm) * X * (Pmᵀ * Piᵀ) := by rw [hPiP, hPt, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  · intro h
    rw [h]
    calc Pm * (Pi * N * Piᵀ) * Pmᵀ = (Pm * Pi) * N * (Piᵀ * Pmᵀ) := by simp only [Matrix.mul_assoc]
      _ = N := by rw [hPP, hPt', Matrix.one_mul, Matrix.mul_one]

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem conj_form_iff (P : GL (Fin 4) F) (z : SL(4, F)) (N : Matrix (Fin 4) (Fin 4) F) :
    ((((slConjugation 4 F P).toMonoidHom z : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * N *
      (((slConjugation 4 F P).toMonoidHom z : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)ᵀ = N) ↔
    ((z : Matrix (Fin 4) (Fin 4) F) * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * N *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) * (z : Matrix (Fin 4) (Fin 4) F)ᵀ =
      ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * N * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) := by
  rw [coe_conj]
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have key : Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi * N * (Pm * (z : Matrix (Fin 4) (Fin 4) F) * Pi)ᵀ =
      Pm * ((z : Matrix (Fin 4) (Fin 4) F) * (Pi * N * Piᵀ) * (z : Matrix (Fin 4) (Fin 4) F)ᵀ) * Pmᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [key]
  exact conj_form_aux hPP hPiP

end Transport

section Util

variable {F : Type} [Field F]

theorem exists_rho [Finite F] (hF4 : Nat.card F % 4 = 3) (h7 : 7 ≤ Nat.card F) :
    ∃ ρ : Fˣ, (ρ : F) ^ 4 ≠ 1 ∧ (ρ : F) ^ 2 + 1 ≠ 0 ∧ (ρ : F) ^ 4 + 1 ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro h
    have h1 : g ^ 4 = 1 := Units.ext (by simpa using h)
    have h2 : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    have h4 : Nat.card Fˣ = Nat.card F - 1 := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · intro h
    exact not_isSquare_neg_one hF4 ⟨g, by linear_combination (-1 : F) * h⟩
  · intro h
    exact not_isSquare_neg_one hF4 ⟨(g : F) ^ 2, by linear_combination (-1 : F) * h⟩

theorem exists_sign [Finite F] (hF4 : Nat.card F % 4 = 3) (b0 b1 : F) (h0 : b0 ≠ 0) (h1 : b1 ≠ 0) :
    ∃ ε : F, (ε = 1 ∨ ε = -1) ∧ ∃ γ : Fˣ, (γ : F) ^ 2 = -ε * b1 / b0 := by
  by_cases hs : IsSquare (-(b0 * b1))
  · obtain ⟨c, hc⟩ := hs
    have hc0 : c ≠ 0 := fun h => by
      rw [h, mul_zero] at hc
      exact mul_ne_zero h0 h1 (neg_eq_zero.1 hc)
    refine ⟨1, Or.inl rfl, Units.mk0 (c / b0) (div_ne_zero hc0 h0), ?_⟩
    simp only [Units.val_mk0]
    field_simp
    linear_combination -hc
  · have hs' : IsSquare (b0 * b1) := by
      have := isSquare_mul_of_not_isSquare (not_isSquare_neg_one hF4) hs
      simpa using this
    obtain ⟨c, hc⟩ := hs'
    have hc0 : c ≠ 0 := fun h => by
      rw [h, mul_zero] at hc
      exact mul_ne_zero h0 h1 hc
    refine ⟨-1, Or.inr rfl, Units.mk0 (c / b0) (div_ne_zero hc0 h0), ?_⟩
    simp only [Units.val_mk0]
    field_simp
    linear_combination -hc

theorem inv2_diag (h2 : (2 : F) ≠ 0) (H : Matrix (Fin 2) (Fin 2) F) (hH : H * H = 1) (h1 : H ≠ 1) (hm1 : H ≠ -1) :
    ∃ Q : GL (Fin 2) F, H * (Q : Matrix (Fin 2) (Fin 2) F) = (Q : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 0, -1] := by
  have eH := Matrix.eta_fin_two H
  set a := H 0 0 with ha
  set b := H 0 1 with hb
  set c := H 1 0 with hc
  set d := H 1 1 with hd
  have e00 : a * a + b * c = 1 := by
    have := congrFun (congrFun hH 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : a * b + b * d = 0 := by
    have := congrFun (congrFun hH 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e10 : c * a + d * c = 0 := by
    have := congrFun (congrFun hH 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e11 : c * b + d * d = 1 := by
    have := congrFun (congrFun hH 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have htr : d = -a := by
    by_contra hne
    have hne' : a + d ≠ 0 := fun h => hne (by linear_combination h)
    have hb0 : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hne'
    have hc0 : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne'
    have haa : (a - 1) * (a + 1) = 0 := by rw [hb0] at e00; linear_combination e00
    have hdd : (d - 1) * (d + 1) = 0 := by rw [hc0] at e11; linear_combination e11
    rcases mul_eq_zero.1 haa with h | h <;> rcases mul_eq_zero.1 hdd with h' | h'
    · apply h1
      rw [eH, sub_eq_zero.1 h, sub_eq_zero.1 h', hb0, hc0]
      exact Matrix.one_fin_two.symm
    · exact hne' (by linear_combination h + h')
    · exact hne' (by linear_combination h + h')
    · apply hm1
      have ha' : a = -1 := eq_neg_of_add_eq_zero_left h
      have hd' : d = -1 := eq_neg_of_add_eq_zero_left h'
      rw [eH, ha', hd', hb0, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have e2 : (2 : F) * 2 ≠ 0 := mul_ne_zero h2 h2
  by_cases hc0 : c = 0
  · have haa : (a - 1) * (a + 1) = 0 := by rw [hc0] at e00; linear_combination e00
    rcases mul_eq_zero.1 haa with h | h
    · have ha1 : a = 1 := sub_eq_zero.1 h
      have hd1 : d = -1 := by rw [htr, ha1]
      have hdet : (!![2, b; 0, -2] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h; exact e2 (by linear_combination (-1 : F) * h)
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![2, b; 0, -2] hdet, ?_⟩
      show H * !![2, b; 0, -2] = !![2, b; 0, -2] * !![1, 0; 0, -1]
      rw [eH, ha1, hd1, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals ring
    · have ha1 : a = -1 := eq_neg_of_add_eq_zero_left h
      have hd1 : d = 1 := by rw [htr, ha1]; ring
      have hdet : (!![b, -2; 2, 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h; exact e2 (by linear_combination h)
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![b, -2; 2, 0] hdet, ?_⟩
      show H * !![b, -2; 2, 0] = !![b, -2; 2, 0] * !![1, 0; 0, -1]
      rw [eH, ha1, hd1, hc0]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      all_goals ring
  · have hdet : (!![a + 1, a - 1; c, c] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      simp [Matrix.det_fin_two]
      have : (a + 1) * c - (a - 1) * c = 2 * c := by ring
      rw [this]
      exact mul_ne_zero h2 hc0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![a + 1, a - 1; c, c] hdet, ?_⟩
    show H * !![a + 1, a - 1; c, c] = !![a + 1, a - 1; c, c] * !![1, 0; 0, -1]
    rw [eH]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, htr] <;>
      first | ring1 | linear_combination e00

end Util

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
