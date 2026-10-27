module

public import CFSG.GH74.GLS.Stage4.T2SL2Defs

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex Subgroup

variable {F : Type} [Field F]

theorem t2B_mem_uSub {x : SL2 F} : x ∈ uSub F ↔
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
      (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem t2B_mem_lSub {x : SL2 F} : x ∈ lSub F ↔
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := Iff.rfl

theorem t2B_mem_tSub {x : SL2 F} : x ∈ tSub F ↔
    (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem t2B_coe_diagGL_inv (a b : Fˣ) :
    (((diagGL a b : GL (Fin 2) F)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![((a⁻¹ : Fˣ) : F), 0; 0, ((b⁻¹ : Fˣ) : F)] := rfl

theorem t2B_slConj_diag (a b : Fˣ) (x : SL2 F) :
    (slConj (diagGL a b) x : Matrix (Fin 2) (Fin 2) F) =
      !![(x : Matrix (Fin 2) (Fin 2) F) 0 0,
          (a : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 * ((b⁻¹ : Fˣ) : F);
        (b : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0 * ((a⁻¹ : Fˣ) : F),
          (x : Matrix (Fin 2) (Fin 2) F) 1 1] := by
  rw [coe_slConj, t2B_coe_diagGL_inv, coe_diagGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;> simp
  · field_simp
  · field_simp

theorem t2B_negOne_eq : (negOne F : Matrix (Fin 2) (Fin 2) F) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem slConj_one (x : SL2 F) : slConj 1 x = x := by
  apply Subtype.ext
  simp [coe_slConj]

theorem slConj_mul (g h : GL (Fin 2) F) (x : SL2 F) :
    slConj (g * h) x = slConj g (slConj h x) := by
  apply Subtype.ext
  simp [coe_slConj, Matrix.mul_assoc]

theorem slConj_scalar (c : Fˣ) (x : SL2 F) : slConj (diagGL c c) x = x := by
  apply Subtype.ext
  rw [t2B_slConj_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem slConj_negOne (g : GL (Fin 2) F) : slConj g (negOne F) = negOne F := by
  apply Subtype.ext
  rw [coe_slConj, t2B_negOne_eq]
  simp

theorem slConj_diag_tSub (a b : Fˣ) : ∀ h ∈ tSub F, slConj (diagGL a b) h = h := by
  intro h hh
  obtain ⟨h01, h10⟩ := t2B_mem_tSub.1 hh
  apply Subtype.ext
  rw [t2B_slConj_diag]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem slConj_diag_uSub (a b : Fˣ) : ∀ x ∈ uSub F, slConj (diagGL a b) x ∈ uSub F := by
  intro x hx
  obtain ⟨h00, h11, h10⟩ := t2B_mem_uSub.1 hx
  rw [t2B_mem_uSub, t2B_slConj_diag]
  simp [h00, h11, h10]

theorem slConj_diag_lSub (a b : Fˣ) : ∀ x ∈ lSub F, slConj (diagGL a b) x ∈ lSub F := by
  intro x hx
  obtain ⟨h00, h11, h01⟩ := t2B_mem_lSub.1 hx
  rw [t2B_mem_lSub, t2B_slConj_diag]
  simp [h00, h11, h01]

theorem sl2W_mul_slConj_diag (a b : Fˣ) :
    sl2W F * slConj (diagGL a b) (sl2W F)⁻¹ ∈ tSub F := by
  rw [t2B_mem_tSub]
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, t2B_slConj_diag,
    Matrix.adjugate_fin_two]

theorem slConj_dNeg_uSub : ∀ x ∈ uSub F, slConj (dNeg F) x = x⁻¹ := by
  intro x hx
  obtain ⟨h00, h11, h10⟩ := t2B_mem_uSub.1 hx
  apply Subtype.ext
  rw [dNeg, t2B_slConj_diag, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h10]

theorem slConj_dNeg_lSub : ∀ x ∈ lSub F, slConj (dNeg F) x = x⁻¹ := by
  intro x hx
  obtain ⟨h00, h11, h01⟩ := t2B_mem_lSub.1 hx
  apply Subtype.ext
  rw [dNeg, t2B_slConj_diag, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01]

theorem slConj_dNeg_W : slConj (dNeg F) (sl2W F) = (sl2W F)⁻¹ := by
  apply Subtype.ext
  rw [dNeg, t2B_slConj_diag, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem centralizer_dNeg (h2 : (2 : F) ≠ 0) :
    ∀ x : SL2 F, slConj (dNeg F) x = x → x ∈ tSub F := by
  intro x hx
  have h := congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F)) hx
  simp only [dNeg, t2B_slConj_diag] at h
  have h01 : -(x : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    simpa using congrFun (congrFun h 0) 1
  have h10 : -(x : Matrix (Fin 2) (Fin 2) F) 1 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    simpa using congrFun (congrFun h 1) 0
  rw [t2B_mem_tSub]
  exact ⟨(mul_eq_zero.1 (by linear_combination -h01 : (2 : F) * (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0)).resolve_left h2,
    (mul_eq_zero.1 (by linear_combination -h10 : (2 : F) * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)).resolve_left h2⟩

theorem slConj_dNeg_sl2U_ne (h2 : (2 : F) ≠ 0) : slConj (dNeg F) (sl2U 1) ≠ sl2U 1 := by
  intro h
  have hmem : sl2U (1 : F) ∈ uSub F := by rw [t2B_mem_uSub]; simp
  rw [slConj_dNeg_uSub _ hmem] at h
  have h3 : sl2U (1 + 1 : F) = sl2U 0 := by
    rw [sl2U_add, sl2U_zero]
    nth_rewrite 1 [← h]
    exact inv_mul_cancel _
  have h4 := sl2U_injective h3
  rw [one_add_one_eq_two] at h4
  exact h2 h4

theorem eq_scalar_of_slConj_eq (g : GL (Fin 2) F) (h : ∀ x : SL2 F, slConj g x = x) :
    ∃ c : F, (g : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have key : ∀ x : SL2 F, (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
      (x : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    intro x
    have hx := congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F)) (h x)
    simp only [coe_slConj] at hx
    rwa [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one] at hx
  have hU := key (sl2U 1)
  have hL := key (sl2L 1)
  have r : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 0
  have p : (g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 0 1 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hU 0) 1
  have q : (g : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hL 0) 0
  have ps : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -p
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [r, q, ps]
theorem t2B_alg_invol {a b c d : F} (h2 : (2 : F) ≠ 0) (e00 : a * a + b * c = 1)
    (e01 : a * b + b * d = 0) (e10 : c * a + d * c = 0) (e11 : c * b + d * d = 1)
    (hdet : a * d - b * c = 1) : b = 0 ∧ c = 0 ∧ d = a ∧ (a = 1 ∨ a = -1) := by
  have hs : a * (a + d) = 2 := by linear_combination e00 + hdet
  have hne : a + d ≠ 0 := fun h => h2 (by rw [← hs, h, mul_zero])
  have hb : b = 0 :=
    (mul_eq_zero.1 (by linear_combination e01 : b * (a + d) = 0)).resolve_right hne
  have hc : c = 0 :=
    (mul_eq_zero.1 (by linear_combination e10 : c * (a + d) = 0)).resolve_right hne
  subst hb hc
  have had : d = a := by
    have h : (d - a) * (a + d) = 0 := by linear_combination e11 - e00
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right hne)
  subst had
  refine ⟨rfl, rfl, rfl, ?_⟩
  have h : (d - 1) * (d + 1) = 0 := by linear_combination e00
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)


theorem eq_negOne_of_involution (h2 : (2 : F) ≠ 0) {x : SL2 F} (hx : x * x = 1) (hx1 : x ≠ 1) :
    x = negOne F := by
  have hm : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
    simpa [Matrix.SpecialLinearGroup.coe_mul] using
      congrArg (fun y : SL2 F => (y : Matrix (Fin 2) (Fin 2) F)) hx
  have hdet : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact x.2
  obtain ⟨hb, hc, hd, ha⟩ := t2B_alg_invol h2
    (by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 0)
    (by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 0) 1)
    (by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 0)
    (by simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hm 1) 1) hdet
  rcases ha with ha | ha
  · exfalso
    apply hx1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem sq_scalar_trace (M : Matrix (Fin 2) (Fin 2) F) (c : F) (hM : M * M = c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hns : ∀ a : F, M ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) : M.trace = 0 ∧ M.det = -c := by
  have e00 : M 0 0 * M 0 0 + M 0 1 * M 1 0 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 0
  have e01 : M 0 0 * M 0 1 + M 0 1 * M 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 1
  have e10 : M 1 0 * M 0 0 + M 1 1 * M 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 0
  have e11 : M 1 0 * M 0 1 + M 1 1 * M 1 1 = c := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 1
  by_cases ht : M 0 0 + M 1 1 = 0
  · refine ⟨by rw [Matrix.trace_fin_two]; exact ht, ?_⟩
    rw [Matrix.det_fin_two]
    linear_combination (M 0 0) * ht - e00
  · exfalso
    have hb : M 0 1 = 0 :=
      (mul_eq_zero.1 (by linear_combination e01 : M 0 1 * (M 0 0 + M 1 1) = 0)).resolve_right ht
    have hc : M 1 0 = 0 :=
      (mul_eq_zero.1 (by linear_combination e10 : M 1 0 * (M 0 0 + M 1 1) = 0)).resolve_right ht
    have had : M 1 1 = M 0 0 := by
      have h : (M 1 1 - M 0 0) * (M 0 0 + M 1 1) = 0 := by linear_combination e11 - e00
      exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_right ht)
    refine hns (M 0 0) ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]

theorem t2B_coe_dNeg : ((dNeg F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dNeg]

theorem t2B_exists_vec {a b c d : F} (hne : ¬ (b = 0 ∧ c = 0 ∧ d = a)) :
    ∃ u0 u1 : F, c * u0 ^ 2 + (d - a) * (u0 * u1) - b * u1 ^ 2 ≠ 0 := by
  by_cases hc : c = 0
  · by_cases hb : b = 0
    · have hda : d - a ≠ 0 := fun h => hne ⟨hb, hc, sub_eq_zero.1 h⟩
      exact ⟨1, 1, by simpa [hb, hc] using hda⟩
    · exact ⟨0, 1, by simpa [hc] using hb⟩
  · exact ⟨1, 0, by simpa using hc⟩


theorem exists_conj_dNeg (h2 : (2 : F) ≠ 0) {M : GL (Fin 2) F}
    (hM : (M : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) = 1)
    (h1 : (M : Matrix (Fin 2) (Fin 2) F) ≠ 1) (h1' : (M : Matrix (Fin 2) (Fin 2) F) ≠ -1) :
    ∃ P : GL (Fin 2) F, P * M * P⁻¹ = dNeg F := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) F, A = (M : Matrix (Fin 2) (Fin 2) F) := ⟨_, rfl⟩
  rw [← hA] at hM h1 h1'
  have e00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 0
  have e01 : A 0 0 * A 0 1 + A 0 1 * A 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 0) 1
  have e10 : A 1 0 * A 0 0 + A 1 1 * A 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 0
  have e11 : A 1 0 * A 0 1 + A 1 1 * A 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hM 1) 1
  have hne : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = A 0 0) := by
    rintro ⟨hb, hc, hd⟩
    have h : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by linear_combination e00 - A 1 0 * hb
    rcases mul_eq_zero.1 h with h | h
    · apply h1
      have ha : A 0 0 = 1 := sub_eq_zero.1 h
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
    · apply h1'
      have ha : A 0 0 = -1 := eq_neg_of_add_eq_zero_left h
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  obtain ⟨u0, u1, hu⟩ := t2B_exists_vec hne
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 2) (Fin 2) F,
      Q = !![(1 + A 0 0) * u0 + A 0 1 * u1, (1 - A 0 0) * u0 - A 0 1 * u1;
        A 1 0 * u0 + (1 + A 1 1) * u1, -(A 1 0 * u0) + (1 - A 1 1) * u1] := ⟨_, rfl⟩
  have hdet : Q.det ≠ 0 := by
    rw [hQ, Matrix.det_fin_two_of]
    have h : ((1 + A 0 0) * u0 + A 0 1 * u1) * (-(A 1 0 * u0) + (1 - A 1 1) * u1) -
        ((1 - A 0 0) * u0 - A 0 1 * u1) * (A 1 0 * u0 + (1 + A 1 1) * u1) =
        -2 * (A 1 0 * u0 ^ 2 + (A 1 1 - A 0 0) * (u0 * u1) - A 0 1 * u1 ^ 2) := by ring
    rw [h]
    exact mul_ne_zero (neg_ne_zero.2 h2) hu
  refine ⟨(Matrix.GeneralLinearGroup.mkOfDetNeZero Q hdet)⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, t2B_coe_dNeg, ← hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, hQ] <;> simp
  · linear_combination u0 * e00 + u1 * e01
  · linear_combination (-u0) * e00 - u1 * e01
  · linear_combination u0 * e10 + u1 * e11
  · linear_combination (-u0) * e10 - u1 * e11

theorem exists_sqrt_negOne [Finite F] (h : Nat.card F % 4 = 1) : ∃ i : F, i * i = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have h' : Fintype.card F % 4 ≠ 3 := by
    rw [← Nat.card_eq_fintype_card, h]; norm_num
  obtain ⟨i, hi⟩ := FiniteField.isSquare_neg_one_iff.2 h'
  exact ⟨i, hi.symm⟩

theorem isSquare_mul_of_not_isSquare [Finite F] (h2 : (2 : F) ≠ 0) {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  have : Fintype F := Fintype.ofFinite F
  have hF : ringChar F ≠ 2 := fun h => h2 (by
    have := ringChar.of_eq h
    exact_mod_cast CharP.cast_eq_zero F 2)
  have ha0 : a ≠ 0 := by rintro rfl; exact ha IsSquare.zero
  have hb0 : b ≠ 0 := by rintro rfl; exact hb IsSquare.zero
  have hneg : ∀ {x : F}, x ≠ 0 → ¬ IsSquare x → x ^ (Fintype.card F / 2) = -1 := by
    intro x hx hxs
    rcases FiniteField.pow_dichotomy hF hx with h | h
    · exact absurd ((FiniteField.isSquare_iff hF hx).2 h) hxs
    · exact h
  refine (FiniteField.isSquare_iff hF (mul_ne_zero ha0 hb0)).2 ?_
  rw [mul_pow, hneg ha0 ha, hneg hb0 hb]
  norm_num

theorem not_isSquare_negOne [Finite F] (h : Nat.card F % 4 = 3) : ¬ IsSquare (-1 : F) := by
  have : Fintype F := Fintype.ofFinite F
  intro hsq
  have h' := FiniteField.isSquare_neg_one_iff.1 hsq
  rw [← Nat.card_eq_fintype_card, h] at h'
  exact h' rfl

theorem sl2W_mul_slConj_diagGL_one (d : Fˣ) :
    sl2W F * slConj (diagGL 1 d) (sl2W F)⁻¹ = sl2D d := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, t2B_slConj_diag, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [Matrix.adjugate_fin_two]

theorem t2B_slConj_toGL (y z : SL2 F) :
    slConj (Matrix.SpecialLinearGroup.toGL y) z = y * z * y⁻¹ := by
  have hinv : (Matrix.SpecialLinearGroup.toGL y)⁻¹ = Matrix.SpecialLinearGroup.toGL y⁻¹ :=
    (map_inv Matrix.SpecialLinearGroup.toGL y).symm
  apply Subtype.ext
  rw [coe_slConj, hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rfl

theorem isSquare_of_slConj_eq_inner (d : Fˣ) (a : SL2 F)
    (h : ∀ x : SL2 F, slConj (diagGL 1 d) x = a * x * a⁻¹) : IsSquare (d : F) := by
  have hg : ∀ x : SL2 F, slConj (Matrix.SpecialLinearGroup.toGL a⁻¹ * diagGL 1 d) x = x := by
    intro x
    rw [slConj_mul, h x, t2B_slConj_toGL]
    group
  obtain ⟨c, hc⟩ := eq_scalar_of_slConj_eq _ hg
  have hdet := congrArg Matrix.det hc
  rw [Units.val_mul, Matrix.det_mul] at hdet
  simp at hdet
  exact ⟨c, by rw [hdet, sq]⟩

end CFSG.GH74.GLS.Stage4.Rest.T2
