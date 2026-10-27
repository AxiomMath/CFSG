module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo

public section

namespace CFSG.GH74.Generic.BProg.B3.S1DiagActMat

open Matrix

variable {F : Type} [Field F]

@[expose] def IsBD (X : Matrix (Fin 4) (Fin 4) F) : Prop :=
  X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 2 = 0 ∧ X 1 3 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 3 0 = 0 ∧ X 3 1 = 0

@[expose] def tl (X : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 2) (Fin 2) F := !![X 0 0, X 0 1; X 1 0, X 1 1]

theorem isBD_of_commute (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 4) (Fin 4) F}
    (h : X * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * X) : IsBD X := by
  have key : ∀ i j : Fin 4, X i j * (![-1, -1, 1, 1] : Fin 4 → F) j =
      (![-1, -1, 1, 1] : Fin 4 → F) i * X i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have hz : ∀ a : F, a = -a → a = 0 := fun a ha => by
    have : (2 : F) * a = 0 := by linear_combination ha
    exact (mul_eq_zero.1 this).resolve_left h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hz _ (by simpa using key 0 2)
  · exact hz _ (by simpa using key 0 3)
  · exact hz _ (by simpa using key 1 2)
  · exact hz _ (by simpa using key 1 3)
  · exact hz _ (by have := key 2 0; simp at this; exact this.symm)
  · exact hz _ (by have := key 2 1; simp at this; exact this.symm)
  · exact hz _ (by have := key 3 0; simp at this; exact this.symm)
  · exact hz _ (by have := key 3 1; simp at this; exact this.symm)

theorem isBD_mul {X Y : Matrix (Fin 4) (Fin 4) F} (hX : IsBD X) (hY : IsBD Y) : IsBD (X * Y) := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := hX
  obtain ⟨y02, y03, y12, y13, y20, y21, y30, y31⟩ := hY
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_four, *]

theorem tl_mul {X Y : Matrix (Fin 4) (Fin 4) F} (hX : IsBD X) (hY : IsBD Y) :
    tl (X * Y) = tl X * tl Y := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := hX
  obtain ⟨y02, y03, y12, y13, y20, y21, y30, y31⟩ := hY
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tl, Matrix.mul_apply, Fin.sum_univ_four, *]

theorem tl_mul3 {X Y Z : Matrix (Fin 4) (Fin 4) F} (hX : IsBD X) (hZ : IsBD Z) :
    tl (X * Y * Zᵀ) = tl X * tl Y * (tl Z)ᵀ := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := hX
  obtain ⟨z02, z03, z12, z13, z20, z21, z30, z31⟩ := hZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tl, Matrix.mul_apply, Fin.sum_univ_four, *]

theorem scalar_of_commute_pair (h2 : (2 : F) ≠ 0) {A C H : Matrix (Fin 2) (Fin 2) F}
    (hAA : A * A = -1) (hCC : C * C = -1) (hAC : A * C = -(C * A)) (hHA : H * A = A * H)
    (hHC : H * C = C * H) : ∃ c : F, H = c • 1 := by
  by_contra hns
  have hcomm := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hns hHA hHC
  have h1 : C * A = 0 := by
    have h3 : C * A = -(C * A) := by rw [← hAC, hcomm]
    have h4 : (2 : F) • (C * A) = 0 := by
      rw [two_smul]; nth_rewrite 1 [h3]; exact neg_add_cancel _
    exact (smul_eq_zero.1 h4).resolve_left h2
  have h5 : C = 0 := by
    calc C = -(C * (A * A)) := by rw [hAA]; simp
      _ = -((C * A) * A) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [h1]; simp
  rw [h5] at hCC
  have := congrFun (congrFun hCC 0) 0
  simp at this

theorem commute_diagonal_of_block {X : Matrix (Fin 4) (Fin 4) F} (hX : IsBD X) (h01 : X 0 1 = 0)
    (h10 : X 1 0 = 0) (h11 : X 0 0 = X 1 1) (d : Fin 4 → F) (hd : d 2 = d 3) :
    Matrix.diagonal d * X = X * Matrix.diagonal d := by
  obtain ⟨x02, x03, x12, x13, x20, x21, x30, x31⟩ := hX
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [*] <;> ring_nf

theorem zero_of_commute_diag {X : Matrix (Fin 4) (Fin 4) F} (d : Fin 4 → F)
    (h : X * Matrix.diagonal d = Matrix.diagonal d * X) {i j : Fin 4} (hij : d i ≠ d j) :
    X i j = 0 := by
  have := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  have h2 : X i j * (d j - d i) = 0 := by linear_combination this
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (Ne.symm hij))

theorem offdiag_eq_zero_of_commute (h2 : (2 : F) ≠ 0) {X : Matrix (Fin 4) (Fin 4) F}
    (h1 : X * Matrix.diagonal ![-1, -1, 1, 1] = Matrix.diagonal ![-1, -1, 1, 1] * X)
    (h2' : X * Matrix.diagonal ![-1, 1, -1, 1] = Matrix.diagonal ![-1, 1, -1, 1] * X) :
    ∀ i j, i ≠ j → X i j = 0 := by
  have hn : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    have : (2 : F) = 1 - (-1) := by ring
    rw [this, h]; ring
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | (refine zero_of_commute_diag _ h1 ?_; simp [hn, hn.symm]; done)
    | (refine zero_of_commute_diag _ h2' ?_; simp [hn, hn.symm])

theorem skew_form (h2 : (2 : F) ≠ 0) {A : Matrix (Fin 2) (Fin 2) F} {β₀ β₁ : F}
    (hβ₀ : β₀ ≠ 0) (hβ₁ : β₁ ≠ 0) (hAA : A * A = -1)
    (hA : A * Matrix.diagonal ![β₀, β₁] * Aᵀ = Matrix.diagonal ![β₀, β₁]) :
    A 0 0 = 0 ∧ A 1 1 = 0 ∧ A 0 1 * β₁ = -(β₀ * A 1 0) ∧ A 0 1 * A 1 0 = -1 := by
  have hT : Aᵀ * Aᵀ = -1 := by rw [← Matrix.transpose_mul, hAA]; simp
  have hAβ : A * Matrix.diagonal ![β₀, β₁] = -(Matrix.diagonal ![β₀, β₁] * Aᵀ) := by
    have h1 : A * Matrix.diagonal ![β₀, β₁] * (Aᵀ * Aᵀ) = Matrix.diagonal ![β₀, β₁] * Aᵀ := by
      rw [← Matrix.mul_assoc, hA]
    rw [hT, Matrix.mul_neg, Matrix.mul_one] at h1
    rw [← h1]; simp
  have e00 := congrFun (congrFun hAβ 0) 0
  have e11 := congrFun (congrFun hAβ 1) 1
  have e01 := congrFun (congrFun hAβ 0) 1
  have a00 := congrFun (congrFun hAA 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 e01 a00
  have h00 : A 0 0 = 0 := by
    have : (2 : F) * (β₀ * A 0 0) = 0 := by linear_combination e00
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact (mul_eq_zero.1 h).resolve_left hβ₀
  have h11 : A 1 1 = 0 := by
    have : (2 : F) * (β₁ * A 1 1) = 0 := by linear_combination e11
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h2
    · exact (mul_eq_zero.1 h).resolve_left hβ₁
  refine ⟨h00, h11, by linear_combination e01, ?_⟩
  rw [h00] at a00
  linear_combination a00

theorem no_skew_pair (h2 : (2 : F) ≠ 0) {A C : Matrix (Fin 2) (Fin 2) F} {β₀ β₁ : F}
    (hβ₀ : β₀ ≠ 0) (hβ₁ : β₁ ≠ 0) (hAA : A * A = -1) (hCC : C * C = -1) (hAC : A * C = -(C * A))
    (hA : A * Matrix.diagonal ![β₀, β₁] * Aᵀ = Matrix.diagonal ![β₀, β₁])
    (hC : C * Matrix.diagonal ![β₀, β₁] * Cᵀ = Matrix.diagonal ![β₀, β₁]) : False := by
  obtain ⟨a00, a11, ab, abc⟩ := skew_form h2 hβ₀ hβ₁ hAA hA
  obtain ⟨c00, c11, cb, cbc⟩ := skew_form h2 hβ₀ hβ₁ hCC hC
  have e00 := congrFun (congrFun hAC 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, a00, c00] at e00
  have h3 : (A 0 1 * C 1 0 - C 0 1 * A 1 0) * β₁ = 0 := by
    linear_combination (C 1 0) * ab - (A 1 0) * cb
  have h4 : A 0 1 * C 1 0 = C 0 1 * A 1 0 := by
    have := (mul_eq_zero.1 h3).resolve_right hβ₁
    linear_combination this
  have h5 : A 0 1 * C 1 0 = 0 := by
    have : (2 : F) * (A 0 1 * C 1 0) = 0 := by linear_combination e00 + h4
    exact (mul_eq_zero.1 this).resolve_left h2
  rcases mul_eq_zero.1 h5 with h | h
  · rw [h] at abc; simp at abc
  · rw [h] at cbc; simp at cbc

theorem isBD_diagonal (d : Fin 4 → F) : IsBD (Matrix.diagonal d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Matrix.diagonal]

theorem tl_y0 : tl (Matrix.diagonal ![-1, -1, 1, 1] : Matrix (Fin 4) (Fin 4) F) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tl, Matrix.diagonal]

theorem tl_diagonal_of_offdiag {X : Matrix (Fin 4) (Fin 4) F} (h01 : X 0 1 = 0) (h10 : X 1 0 = 0) :
    tl X = Matrix.diagonal ![X 0 0, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tl, Matrix.diagonal, h01, h10]

theorem entries_of_tl_scalar {X : Matrix (Fin 4) (Fin 4) F} {c : F} (h : tl X = c • 1) :
    X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 0 0 = X 1 1 := by
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e00 := congrFun (congrFun h 0) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [tl] at e01 e10 e00 e11
  exact ⟨e01, e10, by rw [e00, e11]⟩

theorem diag_entries_ne_zero {X : Matrix (Fin 4) (Fin 4) F} (hoff : ∀ i j, i ≠ j → X i j = 0)
    (hdet : X.det ≠ 0) : X 0 0 ≠ 0 ∧ X 1 1 ≠ 0 := by
  have hX : X = Matrix.diagonal (fun i => X i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hoff i j hij]; simp [Matrix.diagonal, hij]
  rw [hX, Matrix.det_diagonal, Fin.prod_univ_four] at hdet
  refine ⟨fun h => hdet ?_, fun h => hdet ?_⟩ <;> simp [h]

theorem diagonal_of_offdiag_zero {X : Matrix (Fin 4) (Fin 4) F} (hoff : ∀ i j, i ≠ j → X i j = 0) :
    X = Matrix.diagonal (fun i => X i i) := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [hoff i j hij]; simp [Matrix.diagonal, hij]

theorem sq_diag_entries {G : Matrix (Fin 4) (Fin 4) F} (hoff : ∀ i j, i ≠ j → G i j = 0) {c : F}
    (h : G * G = c • 1) (i : Fin 4) : G i i * G i i = c := by
  have hGd := diagonal_of_offdiag_zero hoff
  have := congrFun (congrFun h i) i
  rw [hGd] at this
  simpa [Matrix.diagonal_mul_diagonal] using this

theorem commute_of_invariant_sign {B : Matrix (Fin 4) (Fin 4) F} (ε : Fin 4 → F)
    (hε : ∀ i, ε i * ε i = 1) (h : Matrix.diagonal ε * B * (Matrix.diagonal ε)ᵀ = B) :
    B * Matrix.diagonal ε = Matrix.diagonal ε * B := by
  have hDD : Matrix.diagonal ε * Matrix.diagonal ε = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hε i]
    · simp [hij]
  rw [Matrix.diagonal_transpose] at h
  calc B * Matrix.diagonal ε
      = (Matrix.diagonal ε * Matrix.diagonal ε) * B * Matrix.diagonal ε := by
        rw [hDD, Matrix.one_mul]
    _ = Matrix.diagonal ε * (Matrix.diagonal ε * B * Matrix.diagonal ε) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.diagonal ε * B := by rw [h]

section Conj

variable (P : GL (Fin 4) F)

@[expose] def cj (X : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X * (P : Matrix (Fin 4) (Fin 4) F)

@[expose] def cjB (B : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B *
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ

theorem coe_mul_inv : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem cj_mul (X Y : Matrix (Fin 4) (Fin 4) F) : cj P (X * Y) = cj P X * cj P Y := by
  unfold cj
  calc ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X * Y) * (P : Matrix (Fin 4) (Fin 4) F)
      = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X *
        ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Y *
        (P : Matrix (Fin 4) (Fin 4) F) := by
        rw [coe_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem cj_gl (x : GL (Fin 4) F) :
    cj P (x : Matrix (Fin 4) (Fin 4) F) = ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  unfold cj
  rw [Units.val_mul, Units.val_mul]

theorem cj_smul_one (c : F) : cj P (c • (1 : Matrix (Fin 4) (Fin 4) F)) = c • 1 := by
  unfold cj
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, coe_inv_mul]

theorem cj_injective : Function.Injective (cj P) := by
  intro X Y h
  have hX : X = (P : Matrix (Fin 4) (Fin 4) F) * cj P X * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    unfold cj
    calc X = ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * X *
          ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [coe_mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hY : Y = (P : Matrix (Fin 4) (Fin 4) F) * cj P Y * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    unfold cj
    calc Y = ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Y *
          ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [coe_mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hX, hY, h]

theorem cj_invariant {X B : Matrix (Fin 4) (Fin 4) F} (h : X * B * Xᵀ = B) :
    cj P X * cjB P B * (cj P X)ᵀ = cjB P B := by
  unfold cj cjB
  have hT : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, coe_mul_inv, Matrix.transpose_one]
  calc ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X * (P : Matrix (Fin 4) (Fin 4) F) *
        (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B *
          ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) *
        (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X * (P : Matrix (Fin 4) (Fin 4) F))ᵀ
      = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X *
        ((P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * B *
        (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ) *
        Xᵀ * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (X * B * Xᵀ) *
        ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        rw [coe_mul_inv, hT, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

theorem det_cjB_ne_zero (B : GL (Fin 4) F) :
    (cjB P (B : Matrix (Fin 4) (Fin 4) F)).det ≠ 0 := by
  unfold cjB
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h1 := ((Matrix.isUnit_iff_isUnit_det _).1 (P⁻¹).isUnit).ne_zero
  have h2 := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).ne_zero
  exact mul_ne_zero (mul_ne_zero h1 h2) h1

end Conj

end CFSG.GH74.Generic.BProg.B3.S1DiagActMat
