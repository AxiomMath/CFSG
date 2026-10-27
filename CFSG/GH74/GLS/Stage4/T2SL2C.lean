module

public import CFSG.GH74.GLS.Stage4.T2SL2A
public import CFSG.GH74.GLS.Stage4.T2SL2B

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.T2

open CFSG.GH74.GLS.Stage4.Hex Subgroup

variable {F : Type} [Field F]

theorem t2C_det_diagGL (a b : Fˣ) :
    Matrix.GeneralLinearGroup.det (diagGL a b : GL (Fin 2) F) = a * b := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem t2C_mul_diagGL (a b c e : Fˣ) :
    (diagGL a b : GL (Fin 2) F) * diagGL c e = diagGL (a * c) (b * e) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem t2C_diagGL_central (c : Fˣ) (g : GL (Fin 2) F) :
    (diagGL c c : GL (Fin 2) F) * g = g * diagGL c c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem t2C_toGL_sl2D (t : Fˣ) :
    Matrix.SpecialLinearGroup.toGL (sl2D t : SL2 F) = diagGL t t⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def adjSL (τ : GL (Fin 2) F) : SL2 F :=
  ⟨((diagGL 1 (Matrix.GeneralLinearGroup.det τ) * τ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    have h1 : Matrix.GeneralLinearGroup.det
        (diagGL 1 (Matrix.GeneralLinearGroup.det τ) * τ⁻¹ : GL (Fin 2) F) = 1 := by
      rw [map_mul, map_inv, t2C_det_diagGL]; simp
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h1]
    rfl⟩

theorem toGL_adjSL (τ : GL (Fin 2) F) :
    Matrix.SpecialLinearGroup.toGL (adjSL τ) = diagGL 1 (Matrix.GeneralLinearGroup.det τ) * τ⁻¹ := by
  ext i j
  rfl

theorem slConj_injective (g : GL (Fin 2) F) : Function.Injective (slConj g) := by
  intro x y h
  have := congrArg (slConj g⁻¹) h
  rwa [← slConj_mul, ← slConj_mul, inv_mul_cancel, slConj_one, slConj_one] at this

theorem slConj_surjective (g : GL (Fin 2) F) : Function.Surjective (slConj g) := by
  intro y
  refine ⟨slConj g⁻¹ y, ?_⟩
  rw [← slConj_mul, mul_inv_cancel, slConj_one]

theorem adjSL_conj (τ : GL (Fin 2) F) (x : SL2 F) :
    adjSL τ * slConj τ x * (adjSL τ)⁻¹ =
      slConj (diagGL 1 (Matrix.GeneralLinearGroup.det τ)) x := by
  rw [← t2B_slConj_toGL, ← slConj_mul, toGL_adjSL, inv_mul_cancel_right]

theorem adjSL_dNeg : adjSL (dNeg F) = 1 := by
  apply Subtype.ext
  show ((diagGL 1 (Matrix.GeneralLinearGroup.det (dNeg F)) * (dNeg F)⁻¹ : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = 1
  have : Matrix.GeneralLinearGroup.det (dNeg F : GL (Fin 2) F) = -1 := by
    unfold dNeg; rw [t2C_det_diagGL]; simp
  rw [this]
  have h2 : (diagGL 1 (-1) : GL (Fin 2) F) = dNeg F := rfl
  rw [h2, mul_inv_cancel]
  rfl

theorem t2C_coe_toGL_slConj (g : GL (Fin 2) F) (x : SL2 F) :
    Matrix.SpecialLinearGroup.toGL (slConj g x) = g * Matrix.SpecialLinearGroup.toGL x * g⁻¹ := by
  ext i j
  rfl

theorem adjSL_mul_conj_self (τ : GL (Fin 2) F)
    (hτ : (τ : Matrix (Fin 2) (Fin 2) F) * (τ : Matrix (Fin 2) (Fin 2) F) =
      (-((Matrix.GeneralLinearGroup.det τ : Fˣ) : F)) • (1 : Matrix (Fin 2) (Fin 2) F)) :
    adjSL τ * slConj τ (adjSL τ) = sl2D (-(Matrix.GeneralLinearGroup.det τ)⁻¹) := by
  set d : Fˣ := Matrix.GeneralLinearGroup.det τ with hd
  have hττ : τ * τ = diagGL (-d) (-d) := by
    ext i j
    have := congrFun (congrFun hτ i) j
    fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, t2C_coe_toGL_slConj, toGL_adjSL, t2C_toGL_sl2D]
  have e : diagGL 1 d * τ⁻¹ * (τ * (diagGL 1 d * τ⁻¹) * τ⁻¹) =
      diagGL 1 d * diagGL 1 d * (τ * τ)⁻¹ := by group
  rw [e, hττ, t2C_mul_diagGL]
  have hinv : (diagGL (-d) (-d) : GL (Fin 2) F)⁻¹ = diagGL (-d)⁻¹ (-d)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right
    rw [t2C_mul_diagGL]
    simp
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hinv, t2C_mul_diagGL]
  congr 1 <;> simp

theorem sq_eq_neg_det_of_slConj_sq (τ : GL (Fin 2) F)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det τ : Fˣ) : F))
    (hsq : ∀ x : SL2 F, slConj (τ * τ) x = x) :
    (τ : Matrix (Fin 2) (Fin 2) F) * (τ : Matrix (Fin 2) (Fin 2) F) =
      (-((Matrix.GeneralLinearGroup.det τ : Fˣ) : F)) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨c, hc⟩ := eq_scalar_of_slConj_eq (τ * τ) hsq
  have hc' : (τ : Matrix (Fin 2) (Fin 2) F) * (τ : Matrix (Fin 2) (Fin 2) F) =
      c • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul]; exact hc
  have hnonscalar : ∀ a : F, (τ : Matrix (Fin 2) (Fin 2) F) ≠ a • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro a ha
    apply hns
    refine ⟨a, ?_⟩
    have := congrArg Matrix.det ha
    simp at this
    rw [Matrix.GeneralLinearGroup.val_det_apply, this]
    simp [sq]
  obtain ⟨-, hdet⟩ := sq_scalar_trace _ c hc' hnonscalar
  rw [hc', Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  linear_combination hdet

theorem exists_slConj_split (h2 : (2 : F) ≠ 0) (τ : GL (Fin 2) F)
    (hns : ¬ IsSquare ((Matrix.GeneralLinearGroup.det τ : Fˣ) : F))
    (hsq : ∀ x : SL2 F, slConj (τ * τ) x = x)
    (hsplit : IsSquare (-((Matrix.GeneralLinearGroup.det τ : Fˣ) : F))) :
    ∃ P : GL (Fin 2) F, ∀ x : SL2 F, slConj (P * τ * P⁻¹) x = slConj (dNeg F) x := by
  have hτsq := sq_eq_neg_det_of_slConj_sq τ hns hsq
  obtain ⟨μ, hμ⟩ := hsplit
  set d : Fˣ := Matrix.GeneralLinearGroup.det τ with hd
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    have : ((d : Fˣ) : F) = 0 := by simp at hμ
    exact d.ne_zero this
  let μu : Fˣ := Units.mk0 μ hμ0
  have hττ : τ * τ = diagGL (-d) (-d) := by
    ext i j
    have := congrFun (congrFun hτsq i) j
    fin_cases i <;> fin_cases j <;> simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hμu : μu * μu = -d := by
    apply Units.ext
    simp [μu, hμ]
  let M : GL (Fin 2) F := diagGL μu⁻¹ μu⁻¹ * τ
  have hτM : τ = diagGL μu μu * M := by
    simp only [M]
    rw [← mul_assoc, t2C_mul_diagGL]
    simp
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hMM : M * M = 1 := by
    have e : M * M = diagGL μu⁻¹ μu⁻¹ * diagGL μu⁻¹ μu⁻¹ * (τ * τ) := by
      simp only [M]
      rw [mul_assoc, ← mul_assoc τ, ← t2C_diagGL_central μu⁻¹ τ, mul_assoc, ← mul_assoc]
    rw [e, hττ, t2C_mul_diagGL, t2C_mul_diagGL]
    have hμF : ((d : Fˣ) : F) = -((μu : F) * (μu : F)) := by
      have := congrArg (fun u : Fˣ => (u : F)) hμu
      simp only [Units.val_mul, Units.val_neg] at this
      linear_combination this
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    all_goals (rw [hμF]; field_simp)
  have hτns : ∀ a : F, (τ : Matrix (Fin 2) (Fin 2) F) ≠ a • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro a ha
    apply hns
    refine ⟨a, ?_⟩
    have := congrArg Matrix.det ha
    simp at this
    rw [Matrix.GeneralLinearGroup.val_det_apply, this]
    simp [sq]
  have hM1 : (M : Matrix (Fin 2) (Fin 2) F) ≠ 1 := by
    intro hM
    apply hτns (μ)
    have : (τ : Matrix (Fin 2) (Fin 2) F) = (diagGL μu μu * M : GL (Fin 2) F) := by rw [← hτM]
    rw [this, Units.val_mul, hM, Matrix.mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [μu]
  have hM1' : (M : Matrix (Fin 2) (Fin 2) F) ≠ -1 := by
    intro hM
    apply hτns (-μ)
    have : (τ : Matrix (Fin 2) (Fin 2) F) = (diagGL μu μu * M : GL (Fin 2) F) := by rw [← hτM]
    rw [this, Units.val_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [μu]
  have hMM' : (M : Matrix (Fin 2) (Fin 2) F) * (M : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, hMM]; rfl
  obtain ⟨P, hP⟩ := exists_conj_dNeg h2 hMM' hM1 hM1'
  refine ⟨P, fun x => ?_⟩
  have e : P * τ * P⁻¹ = diagGL μu μu * dNeg F := by
    rw [hτM, ← hP]
    have h5 := t2C_diagGL_central μu P
    calc P * (diagGL μu μu * M) * P⁻¹ = (P * diagGL μu μu) * M * P⁻¹ := by group
      _ = (diagGL μu μu * P) * M * P⁻¹ := by rw [h5]
      _ = diagGL μu μu * (P * M * P⁻¹) := by group
  rw [e, slConj_mul, slConj_scalar]

theorem slConj_sqrt_negOne (ι : Fˣ) (hι : (ι : F) * (ι : F) = -1) (x : SL2 F) :
    sl2D ι * x * (sl2D ι)⁻¹ = slConj (dNeg F) x := by
  rw [← t2B_slConj_toGL, t2C_toGL_sl2D]
  have hιι : ι * ι = -1 := by
    apply Units.ext
    simpa using hι
  have hinv : ι⁻¹ = -ι := inv_eq_of_mul_eq_one_right (by rw [mul_neg, hιι]; simp)
  have e : (diagGL ι ι⁻¹ : GL (Fin 2) F) = diagGL ι ι * dNeg F := by
    unfold dNeg
    rw [t2C_mul_diagGL, hinv]
    simp
  rw [e, slConj_mul, slConj_scalar]

theorem sl2D_sq_of_sqrt (ι : Fˣ) (hι : (ι : F) * (ι : F) = -1) : sl2D ι * sl2D ι = negOne F := by
  have hιι : ι * ι = -1 := by
    apply Units.ext
    simpa using hι
  rw [sl2D_mul, hιι, sl2D_neg_one]

theorem exists_unit_sqrt_negOne [Finite F] (h : Nat.card F % 4 = 1) :
    ∃ ι : Fˣ, (ι : F) * (ι : F) = -1 := by
  obtain ⟨i, hi⟩ := exists_sqrt_negOne (F := F) h
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  exact ⟨Units.mk0 i hi0, by simpa using hi⟩

theorem two_ne_zero_of_odd_card [Finite F] (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h' : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.1 h
  have hne : ringChar F ≠ 2 := fun hc => by
    have := (FiniteField.even_card_iff_char_two).1 hc
    omega
  exact Ring.two_ne_zero hne

theorem minFac_card_eq_ringChar [Finite F] : (Nat.card F).minFac = ringChar F := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  rw [Nat.card_eq_fintype_card, hn]
  exact hp.pow_minFac n.ne_zero

end CFSG.GH74.GLS.Stage4.Rest.T2
