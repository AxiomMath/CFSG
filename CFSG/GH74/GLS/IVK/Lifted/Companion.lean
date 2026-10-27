module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Matrix

theorem companion_exists_vec {F : Type} [Field F] (B : Matrix (Fin 2) (Fin 2) F)
    (hnonscalar : ∀ r : F, B ≠ r • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ w0 w1 : F, B 1 0 * w0 ^ 2 + (B 1 1 - B 0 0) * w0 * w1 - B 0 1 * w1 ^ 2 ≠ 0 := by
  by_contra h
  have h' : ∀ w0 w1 : F, B 1 0 * w0 ^ 2 + (B 1 1 - B 0 0) * w0 * w1 - B 0 1 * w1 ^ 2 = 0 :=
    fun w0 w1 => not_not.mp fun hne => h ⟨w0, w1, hne⟩
  have h1 := h' 1 0
  have h2 := h' 0 1
  have h3 := h' 1 1
  apply hnonscalar (B 0 0)
  have e10 : B 1 0 = 0 := by linear_combination h1
  have e01 : B 0 1 = 0 := by linear_combination -h2
  have e11 : B 1 1 = B 0 0 := by linear_combination h3 - h1 - h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e10, e01, e11]

theorem companion_conj {F : Type} [Field F] (B : Matrix (Fin 2) (Fin 2) F) (hB : B.det = 1)
    (hnonscalar : ∀ r : F, B ≠ r • (1 : Matrix (Fin 2) (Fin 2) F)) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, IsUnit P ∧
      B * P = P * !![0, -1; 1, B 0 0 + B 1 1] := by
  obtain ⟨w0, w1, hD⟩ := companion_exists_vec B hnonscalar
  refine ⟨!![w0, B 0 0 * w0 + B 0 1 * w1; w1, B 1 0 * w0 + B 1 1 * w1], ?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    intro h
    apply hD
    linear_combination h
  · rw [Matrix.det_fin_two] at hB
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-w0) * hB
    · linear_combination (-w1) * hB

theorem companion_pow_iff {M : Type*} [Monoid M] {B C P : M} (hP : IsUnit P) (h : B * P = P * C)
    (n : ℕ) : B ^ n = 1 ↔ C ^ n = 1 := by
  have hn : P * C ^ n = B ^ n * P := SemiconjBy.pow_right h.symm n
  constructor
  · intro h1
    refine hP.mul_right_inj.mp ?_
    rw [hn, h1, one_mul, mul_one]
  · intro h1
    refine hP.mul_left_inj.mp ?_
    rw [← hn, h1, mul_one, one_mul]

theorem exists_sl_companion_order {F : Type} [Field F] (F₀ : Subfield F)
    (b : SpecialLinearGroup (Fin 2) F)
    (hnonscalar : ∀ r : F, (b : Matrix (Fin 2) (Fin 2) F) ≠ r • (1 : Matrix (Fin 2) (Fin 2) F))
    (htr : (b : Matrix (Fin 2) (Fin 2) F) 0 0 + (b : Matrix (Fin 2) (Fin 2) F) 1 1 ∈ F₀) :
    ∃ c : SpecialLinearGroup (Fin 2) ↥F₀, orderOf c = orderOf b := by
  obtain ⟨P, hP, hbP⟩ := companion_conj (b : Matrix (Fin 2) (Fin 2) F) b.2 hnonscalar
  let c : SpecialLinearGroup (Fin 2) ↥F₀ :=
    ⟨!![0, -1; 1, (⟨_, htr⟩ : ↥F₀)], by simp [Matrix.det_fin_two]⟩
  refine ⟨c, ?_⟩
  have hb : orderOf b = orderOf (b : Matrix (Fin 2) (Fin 2) F) :=
    (orderOf_injective (Matrix.SpecialLinearGroup.coeMonoidHom (ι := Fin 2) (R := F))
      Matrix.SpecialLinearGroup.coeMonoidHom_injective b).symm
  let φ : SpecialLinearGroup (Fin 2) ↥F₀ →* Matrix (Fin 2) (Fin 2) F :=
    Matrix.SpecialLinearGroup.coeMonoidHom.comp (Matrix.SpecialLinearGroup.map F₀.subtype)
  have hφ : ∀ x : SpecialLinearGroup (Fin 2) ↥F₀,
      φ x = (x : Matrix (Fin 2) (Fin 2) ↥F₀).map F₀.subtype := fun x => rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    rw [hφ, hφ] at hxy
    exact Subtype.ext (Matrix.map_injective F₀.subtype.injective hxy)
  have hc : orderOf c = orderOf (!![0, -1; 1, (b : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (b : Matrix (Fin 2) (Fin 2) F) 1 1] : Matrix (Fin 2) (Fin 2) F) := by
    rw [← orderOf_injective φ hinj c, hφ]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c]
  rw [hc, hb]
  exact orderOf_eq_orderOf_iff.mpr fun n => (companion_pow_iff hP hbP n).symm

end CFSG.GH74.GLS.IVK.Lifted
