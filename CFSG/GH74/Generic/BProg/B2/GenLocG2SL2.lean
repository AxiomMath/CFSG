module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Torus
import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections
import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

namespace GenLocG2SL2

variable {F : Type} [Field F]

@[expose] noncomputable def antiW (b : Fˣ) : SL(2, F) :=
  ⟨!![0, (b : F); -((b⁻¹ : Fˣ) : F), 0], by
    rw [Matrix.det_fin_two_of]; simp⟩

theorem coe_antiW (b : Fˣ) : ((antiW b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    !![0, (b : F); -((b⁻¹ : Fˣ) : F), 0] := rfl

theorem exists_sq_add_sq [Finite F] (h2 : ringChar F ≠ 2) (c : F) :
    ∃ x y : F, x ^ 2 + y ^ 2 = c := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨x, y, h⟩ := CFSG.PSL2Table.exists_normForm_eq h2 (ν := (-1 : F)) (by simp) c
  exact ⟨x, y, by linear_combination h⟩

theorem antiW_isConj [Finite F] (h2 : ringChar F ≠ 2) (b b' : Fˣ) :
    IsConj (antiW b) (antiW b') := by
  obtain ⟨w, s, hws⟩ := exists_sq_add_sq h2 ((b : F) / (b' : F))
  set ν : F := (b' : F) / (b : F) with hν
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  have hb0' : (b' : F) ≠ 0 := b'.ne_zero
  have hdet : ν * (w ^ 2 + s ^ 2) = 1 := by
    rw [hws, hν]; field_simp
  let h : SL(2, F) := ⟨!![ν * w, -((b : F) * b' * (s / b)); s / b, w], by
    rw [Matrix.det_fin_two_of]
    have : (b : F) * b' * (s / b) * (s / b) = ν * s ^ 2 := by
      rw [hν]; field_simp
    linear_combination hdet + this⟩
  rw [isConj_iff]
  refine ⟨h, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show !![ν * w, -((b : F) * b' * (s / b)); s / b, w] * !![0, (b : F); -((b⁻¹ : Fˣ) : F), 0] =
    !![0, (b' : F); -((b'⁻¹ : Fˣ) : F), 0] * !![ν * w, -((b : F) * b' * (s / b)); s / b, w]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hν] <;> field_simp

theorem sq_eq_neg_one_of_orderOf_four (h2 : (2 : F) ≠ 0) {x : SL(2, F)} (hx : orderOf x = 4) :
    (x : Matrix (Fin 2) (Fin 2) F) * x = -1 := by
  have h4 : (x ^ 2) ^ 2 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    rw [← pow_mul]; exact this
  have h1 : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    omega
  have := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (x ^ 2) h4 h1
  rw [sq, Matrix.SpecialLinearGroup.coe_mul] at this
  exact this

theorem exists_conj_antiW (h2 : (2 : F) ≠ 0) {x : SL(2, F)} (hx : orderOf x = 4) :
    ∃ b : Fˣ, IsConj x (antiW b) := by
  have hM := sq_eq_neg_one_of_orderOf_four h2 hx
  have hM' : (x : Matrix (Fin 2) (Fin 2) F) * x = (-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [hM]; simp
  have hns : ∀ c : F, (x : Matrix (Fin 2) (Fin 2) F) ≠ c • 1 := by
    intro c hc
    have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := x.2
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
    rw [hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one] at hM'
    have e := congrFun (congrFun hM' 0) 0
    simp at e
    apply h2
    have hc2 : c ^ 2 = 1 := by simpa using hdet
    have : c * c = -1 := e
    linear_combination this - hc2
  obtain ⟨R, b, c, hb, hc, hR⟩ := exists_antidiag_conj h2 (x : Matrix (Fin 2) (Fin 2) F) hM'
    (by simp) hns
  have hdet : (x : Matrix (Fin 2) (Fin 2) F).det = 1 := x.2
  have hdet' : (!![0, b; c, 0] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← hR, Matrix.det_mul, Matrix.det_mul, hdet, R.2]
    have : ((R⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).det = 1 := (R⁻¹).2
    rw [this]; ring
  rw [Matrix.det_fin_two_of] at hdet'
  have hc' : c = -(b⁻¹) := by
    field_simp
    linear_combination -hdet'
  refine ⟨Units.mk0 b hb, ?_⟩
  rw [isConj_iff]
  refine ⟨R, ?_⟩
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hR, coe_antiW, hc']
  simp

end GenLocG2SL2

section L3

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem sl2_order_four_isConj (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) {a b : SL(2, F)}
    (ha : orderOf a = 4) (hb : orderOf b = 4) : IsConj a b := by
  have hchar : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
    rw [ringChar.eq F p]
    exact hp2
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨b₁, h₁⟩ := GenLocG2SL2.exists_conj_antiW h2 ha
  obtain ⟨b₂, h₂⟩ := GenLocG2SL2.exists_conj_antiW h2 hb
  exact h₁.trans ((GenLocG2SL2.antiW_isConj hchar b₁ b₂).trans h₂.symm)

end L3

end CFSG.GH74.Generic.BProg.B2
