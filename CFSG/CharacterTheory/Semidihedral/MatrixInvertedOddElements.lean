module

public import CFSG.CharacterTheory.Semidihedral.AllPrimeTIFacts.Matrix

public section

namespace CFSG.Semidihedral.MatrixTorus

noncomputable section

open Matrix CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.AllPrime.QDTI

variable {F : Type} [Field F]

private def mio_diagHom (F : Type) [Field F] : Fˣ →* SL F where
  toFun α := ⟨Matrix.diagonal ![(α : F), ((α⁻¹ : Fˣ) : F)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp⟩
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal ![((1 : Fˣ) : F), (((1 : Fˣ)⁻¹ : Fˣ) : F)] = 1
    rw [← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  map_mul' α β := by
    apply Subtype.ext
    change Matrix.diagonal ![((α * β : Fˣ) : F), (((α * β)⁻¹ : Fˣ) : F)] =
      Matrix.diagonal ![(α : F), ((α⁻¹ : Fˣ) : F)] * Matrix.diagonal ![(β : F), ((β⁻¹ : Fˣ) : F)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

private theorem mio_diagHom_val (α : Fˣ) :
    (mio_diagHom F α).1 = Matrix.diagonal ![(α : F), ((α⁻¹ : Fˣ) : F)] := rfl

private theorem mio_diagHom_injective : Function.Injective (mio_diagHom F) := by
  intro α β h
  have h1 := congrArg (fun X : SL F => X.1 0 0) h
  simp only [mio_diagHom_val, Matrix.diagonal_apply_eq, Matrix.cons_val_zero] at h1
  exact Units.ext h1

theorem exists_beta_eq_inv_orderOf {F : Type} [Field F] [Finite F]
    (a : Fˣ) (ha : ¬IsSquare a) (hodd : Odd (Nat.card F)) {s : ℕ} (hs : s.Prime) (_hs2 : s ≠ 2)
    (hdvd : s ∣ Nat.card F - 1 ∨ s ∣ Nat.card F + 1 ∨ (Nat.card F % 4 = 3 ∧ CharP F s)) :
    ∃ Y : Matrix.SpecialLinearGroup (Fin 2) F,
      CFSG.Semidihedral.MatrixCoverData.beta F a Y = Y⁻¹ ∧ orderOf Y = s := by
  have : Fact s.Prime := ⟨hs⟩
  rcases hdvd with h1 | h2 | ⟨h3, hchar⟩
  ·
    obtain ⟨α, hα⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) s (by rwa [Nat.card_units])
    refine ⟨mio_diagHom F α, ?_, ?_⟩
    · rw [beta_eq_inv_iff, mio_diagHom_val, Matrix.diagonal_apply_ne _ (by decide),
        Matrix.diagonal_apply_ne _ (by decide), mul_zero]
    · rw [orderOf_injective _ mio_diagHom_injective, hα]
  ·
    have hns : ¬IsSquare (-(((-a : Fˣ)) : F)) := by
      rw [Units.val_neg, neg_neg]
      exact fun h => ha ((CFSG.Semidihedral.SemilinearOuterQuotient.isSquare_unit_iff a).mpr h)
    have hcard := nonsplit_torus_card F (-a) hns
    obtain ⟨Y, hY⟩ := exists_prime_orderOf_dvd_card' (G := Torus F (-a)) s (by rwa [hcard])
    refine ⟨(Y : SL F), ?_, by rw [Subgroup.orderOf_coe, hY]⟩
    rw [beta_eq_inv_iff]
    obtain ⟨h01, -⟩ := (mem_torus_iff F (-a) (Y : SL F)).mp Y.2
    rw [h01, Units.val_neg, neg_neg]
  ·
    obtain ⟨l, hl⟩ := (neg_coefficient_square_iff F a hodd ha).mpr h3
    refine ⟨rootHom l (Multiplicative.ofAdd 1), ?_, ?_⟩
    · rw [beta_eq_inv_iff, rootHom_val]
      simp only [toAdd_ofAdd, one_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      linear_combination -hl
    · rw [orderOf_injective _ (rootHom_injective l), orderOf_ofAdd_eq_addOrderOf]
      exact CharP.eq F (CharP.addOrderOf_one F) hchar

end

end CFSG.Semidihedral.MatrixTorus
