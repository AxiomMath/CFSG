module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem antidiag_two : (antidiag 2 : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antidiag]

@[expose] def hypMat (ζ : F) (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :
    Matrix (Fin 2) (Fin 2) F :=
  !![(A 0 0 : F), (A 0 1 : F) * ζ; (A 1 0 : F) * ζ⁻¹, (A 1 1 : F)]

variable {ζ : F}

theorem hypMat_mul (hζ0 : ζ ≠ 0) (A B : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :
    hypMat ζ (A * B) = hypMat ζ A * hypMat ζ B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem hypMat_one : hypMat ζ (1 : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypMat]

theorem det_hypMat (hζ0 : ζ ≠ 0) (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :
    (hypMat ζ A).det = ((A.det : fixedSubfield F p f) : F) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [hypMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Subfield.coe_sub, Subfield.coe_mul]
  field_simp

omit [Finite F] in
theorem conj_entries_of_mem_SU_two {σ : F ≃+* F} {M : GL (Fin 2) F} (hM : M ∈ SU σ 2) :
    σ ((M : Matrix (Fin 2) (Fin 2) F) 0 0) = (M : Matrix (Fin 2) (Fin 2) F) 0 0 ∧
      σ ((M : Matrix (Fin 2) (Fin 2) F) 1 1) = (M : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
      σ ((M : Matrix (Fin 2) (Fin 2) F) 0 1) = -(M : Matrix (Fin 2) (Fin 2) F) 0 1 ∧
      σ ((M : Matrix (Fin 2) (Fin 2) F) 1 0) = -(M : Matrix (Fin 2) (Fin 2) F) 1 0 := by
  obtain ⟨hdet, hiso⟩ := mem_SU.1 hM
  set m := (M : Matrix (Fin 2) (Fin 2) F)
  rw [antidiag_two] at hiso
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hiso 0) 0
  have e01 := congrFun (congrFun hiso 0) 1
  have e10 := congrFun (congrFun hiso 1) 0
  have e11 := congrFun (congrFun hiso 1) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-σ (m 0 0)) * hdet + m 0 0 * e01 - m 0 1 * e00
  · linear_combination (-σ (m 1 1)) * hdet + m 1 1 * e10 - m 1 0 * e11
  · linear_combination m 0 0 * e11 - m 0 1 * e10 - σ (m 0 1) * hdet
  · linear_combination m 1 1 * e00 - m 1 0 * e01 - σ (m 1 0) * hdet

section Hyp

variable (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution F p f ζ = -ζ)
include hζ0 hζ

omit hζ0 in
theorem conjTr_hypMat (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :
    conjTr (unitaryInvolution F p f) (hypMat ζ A) =
      !![(A 0 0 : F), -((A 1 0 : F) * ζ⁻¹); -((A 0 1 : F) * ζ), (A 1 1 : F)] := by
  have hfix : ∀ a : fixedSubfield F p f, unitaryInvolution F p f (a : F) = a := fun a => a.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [conjTr, hypMat, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, map_mul, map_inv₀, hfix, hζ, Fin.mk_zero, Fin.mk_one,
      Fin.isValue] <;> ring

theorem hypMat_isometry {A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)} (hA : A.det = 1) :
    conjTr (unitaryInvolution F p f) (hypMat ζ A) * antidiag 2 * hypMat ζ A = antidiag 2 := by
  have hdet : ((A 0 0 : F) * A 1 1 - A 0 1 * A 1 0) = 1 := by
    have := congrArg (fun x : fixedSubfield F p f => (x : F)) hA
    simpa [Matrix.det_fin_two] using this
  rw [conjTr_hypMat hζ, antidiag_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet

@[expose] noncomputable def hypElt (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f)) :
    SU (unitaryInvolution F p f) 2 :=
  ⟨⟨hypMat ζ (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)),
      hypMat ζ ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f)) :
        Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)),
      by rw [← hypMat_mul hζ0, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, hypMat_one],
      by rw [← hypMat_mul hζ0, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, hypMat_one]⟩,
    by rw [Units.val_mk, det_hypMat hζ0, A.2]; rfl,
    hypMat_isometry hζ0 hζ A.2⟩

theorem coe_hypElt (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f)) :
    ((hypElt hζ0 hζ A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      hypMat ζ (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :=
  rfl

@[expose] noncomputable def hypHom :
    Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f) →* SU (unitaryInvolution F p f) 2 :=
  MonoidHom.mk' (hypElt hζ0 hζ) fun A B => Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_hypElt, coe_hypElt, coe_hypElt,
      Matrix.SpecialLinearGroup.coe_mul, hypMat_mul hζ0]))

theorem coe_hypHom (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f)) :
    ((hypHom hζ0 hζ A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      hypMat ζ (A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f)) :=
  rfl

theorem hypHom_injective : Function.Injective (hypHom hζ0 hζ) := by
  intro A B h
  have h' := congrArg (fun g : SU (unitaryInvolution F p f) 2 =>
    ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
  simp only [coe_hypHom] at h'
  have e00 := congrFun (congrFun h' 0) 0
  have e01 := congrFun (congrFun h' 0) 1
  have e10 := congrFun (congrFun h' 1) 0
  have e11 := congrFun (congrFun h' 1) 1
  simp only [hypMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j
  · exact e00
  · exact mul_right_cancel₀ hζ0 e01
  · exact mul_right_cancel₀ (inv_ne_zero hζ0) e10
  · exact e11

theorem hypHom_surjective : Function.Surjective (hypHom hζ0 hζ) := by
  intro M
  obtain ⟨h00, h11, h01, h10⟩ := conj_entries_of_mem_SU_two M.2
  have hdet := (mem_SU.1 M.2).1
  set m := ((M : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.det_fin_two] at hdet
  have hb : m 0 1 / ζ ∈ fixedSubfield F p f := by
    rw [mem_fixedSubfield, map_div₀, h01, hζ, neg_div_neg_eq]
  have hc : m 1 0 * ζ ∈ fixedSubfield F p f := by
    rw [mem_fixedSubfield, map_mul, h10, hζ, neg_mul_neg]
  let A : Matrix (Fin 2) (Fin 2) (fixedSubfield F p f) :=
    !![⟨m 0 0, h00⟩, ⟨m 0 1 / ζ, hb⟩; ⟨m 1 0 * ζ, hc⟩, ⟨m 1 1, h11⟩]
  have hA : A.det = 1 := by
    apply Subtype.ext
    rw [Matrix.det_fin_two]
    simp only [A, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Subfield.coe_sub, Subfield.coe_mul,
      Subfield.coe_one]
    field_simp
    linear_combination hdet
  refine ⟨⟨A, hA⟩, Subtype.ext (Units.ext ?_)⟩
  show hypMat ζ A = m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hypMat, A] <;> field_simp

@[expose] noncomputable def hypEquiv :
    Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f) ≃* SU (unitaryInvolution F p f) 2 :=
  MulEquiv.ofBijective (hypHom hζ0 hζ) ⟨hypHom_injective hζ0 hζ, hypHom_surjective hζ0 hζ⟩

theorem hypEquiv_apply (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield F p f)) :
    hypEquiv hζ0 hζ A = hypHom hζ0 hζ A :=
  rfl

end Hyp

theorem card_specialLinearGroup_fin_two (k : Type*) [Field k] [Finite k] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  let := Fintype.ofFinite k
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card k ^ 2 - Fintype.card k =
      Fintype.card k * (Fintype.card k - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_SU_two (hF : Nat.card F = (p ^ f) ^ 2) :
    Nat.card (SU (unitaryInvolution F p f) 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  rw [← Nat.card_congr (hypEquiv hζ0 hζ).toEquiv, card_specialLinearGroup_fin_two,
    card_fixedSubfield hF]

end CFSG.LieType.Steinberg
