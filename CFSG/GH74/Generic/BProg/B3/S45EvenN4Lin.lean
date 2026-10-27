module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtBasis

public section

namespace CFSG.GH74.Generic.BProg.B3.S45EvenN4Lin

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
  CFSG.GH74.Generic.BProg.B3.S45EvenN4Eig

variable {F : Type} [Field F]

theorem two_ne_zero_of_card_mod [Finite F] (hF4 : Nat.card F % 4 = 3) : (2 : F) ≠ 0 := by
  intro h0
  have := Fintype.ofFinite F
  have hchar : ringChar F = 2 :=
    CharP.ringChar_of_prime_eq_zero Nat.prime_two (by exact_mod_cast h0)
  have : CharP F 2 := by rw [← hchar]; exact ringChar.charP F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  have h2 : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have h3 : 2 ∣ Nat.card F := by rw [h2]; exact dvd_pow_self 2 (by omega)
  omega

section Nsq

open CFSG.GH74.Generic.BProg.B2.GenLocL4Ext

theorem isSquare_neg_of_not [Finite F] (hF4 : Nat.card F % 4 = 3) {c : F} (hc : ¬ IsSquare c) :
    IsSquare (-c) := by
  classical
  have := Fintype.ofFinite F
  have hneg : ¬ IsSquare (-1 : F) := fun h =>
    (FiniteField.isSquare_neg_one_iff.1 h) (by rwa [← Nat.card_eq_fintype_card])
  by_contra h
  have h1 := quadraticChar_neg_one_iff_not_isSquare.2 hneg
  have h2 := quadraticChar_neg_one_iff_not_isSquare.2 hc
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
  have h3 : quadraticChar F (-c) = 1 := by rw [← neg_one_mul, map_mul, h1, h2]; norm_num
  exact h ((quadraticChar_one_iff_isSquare (neg_ne_zero.2 hc0)).1 h3)

theorem exists_not_mem_span [Finite F] (x : Matrix (Fin 4) (Fin 4) F) (v : Fin 4 → F) :
    ∃ w : Fin 4 → F, ∀ a b : F, w ≠ a • v + b • (x *ᵥ v) := by
  classical
  have := Fintype.ofFinite F
  by_contra hall
  push Not at hall
  have hsurj : Function.Surjective (fun p : F × F => p.1 • v + p.2 • (x *ᵥ v)) := fun w => by
    obtain ⟨a, b, h⟩ := hall w
    exact ⟨(a, b), h.symm⟩
  have hcard := Fintype.card_le_of_surjective _ hsurj
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] at hcard
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have h4 : Fintype.card F ^ 4 = Fintype.card F * Fintype.card F * (Fintype.card F * Fintype.card F) := by
    ring
  have h5 : 4 ≤ Fintype.card F * Fintype.card F := by nlinarith
  rw [h4] at hcard
  nlinarith

theorem colMat_isUnit_of_not_mem {c : F} (hc : ¬ IsSquare c) {x : Matrix (Fin 4) (Fin 4) F}
    (hx : x * x = c • (1 : Matrix (Fin 4) (Fin 4) F)) {v w : Fin 4 → F} (hv : v ≠ 0)
    (hw : ∀ a b : F, w ≠ a • v + b • (x *ᵥ v)) : IsUnit (colMat x v w) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices key : ∀ y, colMat x v w *ᵥ y = 0 → y = 0 by
    intro y z hyz
    exact sub_eq_zero.1 (key (y - z) (by rw [Matrix.mulVec_sub, hyz, sub_self]))
  intro y hy
  rw [colMat_mulVec] at hy
  have hxx : ∀ u : Fin 4 → F, x *ᵥ (x *ᵥ u) = c • u := fun u => by
    rw [Matrix.mulVec_mulVec, hx, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : y 0 • (x *ᵥ v) + y 1 • (c • v) + y 2 • (x *ᵥ w) + y 3 • (c • w) = 0 := by
    have := congrArg (fun u => x *ᵥ u) hy
    simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, hxx, Matrix.mulVec_zero] using this
  have hyw : y 2 = 0 ∧ y 3 = 0 := by
    by_contra hne
    have hν : y 2 * y 2 - c * (y 3 * y 3) ≠ 0 := by
      intro h0
      apply hne
      by_cases h3 : y 3 = 0
      · rw [h3] at h0
        exact ⟨mul_self_eq_zero.1 (by linear_combination h0), h3⟩
      · exfalso
        apply hc
        refine ⟨y 2 / y 3, ?_⟩
        field_simp
        linear_combination (-1 : F) * h0
    have hlin : (y 2 * y 2 - c * (y 3 * y 3)) • w +
        (y 2 * y 0 - c * (y 3 * y 1)) • v + (y 2 * y 1 - y 3 * y 0) • (x *ᵥ v) = 0 := by
      linear_combination (norm := module) y 2 • hy - y 3 • h2
    apply hw (-((y 2 * y 0 - c * (y 3 * y 1)) / (y 2 * y 2 - c * (y 3 * y 3))))
      (-((y 2 * y 1 - y 3 * y 0) / (y 2 * y 2 - c * (y 3 * y 3))))
    have h4 : (y 2 * y 2 - c * (y 3 * y 3)) • w = -((y 2 * y 0 - c * (y 3 * y 1)) • v +
        (y 2 * y 1 - y 3 * y 0) • (x *ᵥ v)) := by
      linear_combination (norm := module) hlin
    have h5 := congrArg (fun u => (y 2 * y 2 - c * (y 3 * y 3))⁻¹ • u) h4
    simp only [smul_smul, inv_mul_cancel₀ hν, one_smul, smul_neg, smul_add] at h5
    rw [h5]
    simp only [div_eq_inv_mul]
    module
  obtain ⟨hy2, hy3⟩ := hyw
  rw [hy2, hy3] at hy
  have h6 : y 0 • v + y 1 • (x *ᵥ v) = 0 := by
    linear_combination (norm := module) hy
  obtain ⟨hy0, hy1⟩ := zero_of_comb hc hx hv h6
  funext k
  fin_cases k <;> simp [hy0, hy1, hy2, hy3]

@[expose] def arN (β c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, β * c, 0, 0; β, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem arN_det {β c : F} (h : β * β * c = -1) : (arN β c).det = 1 := by
  rw [arN, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero]
  have e : (![0, 0, 0, 1] : Fin 4 → F) (Fin.succAbove 1 2) = 1 := rfl
  rw [e]
  linear_combination (-1 : F) * h

theorem arN_sq {β c : F} (h : β * β * c = -1) :
    arN β c * arN β c = !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [arN, Matrix.mul_apply, Fin.sum_univ_four] <;>
    linear_combination h

theorem arN_pow {β c : F} (h : β * β * c = -1) : arN β c * arN β c * (arN β c * arN β c) = 1 := by
  rw [arN_sq h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem arN_sq_ne (h2 : (2 : F) ≠ 0) {β c : F} (h : β * β * c = -1) : arN β c * arN β c ≠ 1 := by
  rw [arN_sq h]
  intro h1
  have := congrFun (congrFun h1 0) 0
  simp at this
  apply h2
  linear_combination -this

theorem arN_comm (β c : F) : arN β c * i0 c = i0 c * arN β c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [arN, i0, Matrix.mul_apply, Fin.sum_univ_four, mul_comm]

@[expose] def arNSL {β c : F} (h : β * β * c = -1) : Matrix.SpecialLinearGroup (Fin 4) F :=
  ⟨arN β c, arN_det h⟩

theorem arNSL_pow {β c : F} (h : β * β * c = -1) : (arNSL h) ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show (arN β c : Matrix (Fin 4) (Fin 4) F) ^ 4 = 1
  calc (arN β c : Matrix (Fin 4) (Fin 4) F) ^ 4 = arN β c * arN β c * (arN β c * arN β c) := by
        simp [pow_succ, Matrix.mul_assoc]
    _ = 1 := arN_pow h

theorem arNSL_sq_ne (h2 : (2 : F) ≠ 0) {β c : F} (h : β * β * c = -1) : (arNSL h) ^ 2 ≠ 1 := by
  intro h1
  apply arN_sq_ne h2 h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F)) h1
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at this
  rw [pow_two] at this
  exact this

theorem exists_order_four_nsq [Finite F] (hF4 : Nat.card F % 4 = 3) {x : Matrix (Fin 4) (Fin 4) F}
    {c : F} (hc : ¬ IsSquare c) (hx : x * x = c • (1 : Matrix (Fin 4) (Fin 4) F)) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 4) F, (a : Matrix (Fin 4) (Fin 4) F) * x = x * a ∧
      a ^ 4 = 1 ∧ a ^ 2 ≠ 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_card_mod hF4
  obtain ⟨r, hr⟩ := isSquare_neg_of_not hF4 hc
  have hc0 : c ≠ 0 := by rintro rfl; exact hc ⟨0, by simp⟩
  have hβ : (r / c) * (r / c) * c = -1 := by
    field_simp
    linear_combination (-1 : F) * hr
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → F, v ≠ 0 := ⟨Pi.single 0 1, fun h => by
    have := congrFun h 0
    simp at this⟩
  obtain ⟨w, hw⟩ := exists_not_mem_span x v
  have hU := colMat_isUnit_of_not_mem hc hx hv hw
  let Bg : GL (Fin 4) F := hU.unit
  have hBg : (Bg : Matrix (Fin 4) (Fin 4) F) = colMat x v w := IsUnit.unit_spec hU
  let φ := CatalogueBHigherLinearAction.slConjugation 4 F Bg
  have hcoe : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      ((φ g : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (Bg : Matrix (Fin 4) (Fin 4) F) * g * ((Bg⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
    fun g => LinearFlag.coe_slConjugation Bg g
  refine ⟨φ (arNSL hβ), ?_, ?_, ?_⟩
  · rw [hcoe]
    refine conj_comm (D := i0 c) Bg.mul_inv Bg.inv_mul ?_ (arN_comm _ c)
    rw [hBg]
    exact colMat_i0 c x hx v w
  · rw [← map_pow, arNSL_pow, map_one]
  · intro h
    apply arNSL_sq_ne h2 hβ
    apply φ.injective
    rw [map_pow, h, map_one]

end Nsq

end CFSG.GH74.Generic.BProg.B3.S45EvenN4Lin
