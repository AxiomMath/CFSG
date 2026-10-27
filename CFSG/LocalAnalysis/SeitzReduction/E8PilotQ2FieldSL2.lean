module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotAlignFieldSL2

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Matrix CFSG.LieType.Steinberg

section SL2

variable {K : Type} [Field K] [CharP K 2]

theorem coe_sl2Upper_mul_sl2Lower_pow_three_zero_one (u v : K) :
    (((sl2Upper u * sl2Lower v) ^ 3 : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) 0 1 = u * (1 + u * v) ^ 2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp [pow_succ, SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
    Fin.sum_univ_two]
  linear_combination (u + u * u * v) * h2

theorem sl2Upper_mul_sl2Lower_inv_pow_three {a : K} (ha : a ≠ 0) :
    (sl2Upper a * sl2Lower a⁻¹) ^ 3 = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_apply,
      Fin.sum_univ_two]
  · linear_combination (a * a⁻¹ * (a * a⁻¹) + 6 * (a * a⁻¹) + 12) * h1 + 6 * h2
  · linear_combination a * (a * a⁻¹ + 5) * h1 + 4 * a * h2
  · linear_combination a⁻¹ * (a * a⁻¹ + 5) * h1 + 4 * a⁻¹ * h2
  · linear_combination (a * a⁻¹ + 4) * h1 + 2 * h2

theorem mul_eq_one_of_sl2Upper_mul_sl2Lower_pow_three {u v : K} (hu : u ≠ 0)
    (h : (sl2Upper u * sl2Lower v) ^ 3 = 1) : u * v = 1 := by
  have h1 := coe_sl2Upper_mul_sl2Lower_pow_three_zero_one u v
  rw [h] at h1
  simp only [SpecialLinearGroup.coe_one, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]
    at h1
  have h2 : (1 + u * v) ^ 2 = 0 := by
    rcases mul_eq_zero.1 h1.symm with h3 | h3
    · exact absurd h3 hu
    · exact h3
  have h3 : 1 + u * v = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
  have h4 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h3 - h4

variable [Finite K]

theorem exists_ringEquiv_of_forall_sl2_of_charTwo {k : Type} [Field k] (ι : k →+* K)
    (β : MulAut (SpecialLinearGroup (Fin 2) K))
    (hx : ∀ c : k, β (sl2Upper (ι c)) = sl2Upper (ι c))
    (hy : ∀ c : k, β (sl2Lower (ι c)) = sl2Lower (ι c)) :
    ∃ ρ : K ≃+* K, (∀ c, ρ (ι c) = ι c) ∧
      ∀ a : K, β (sl2Upper a) = sl2Upper (ρ a) ∧ β (sl2Lower a) = sl2Lower (ρ a) := by
  have hx1 : β (sl2Upper 1) = sl2Upper 1 := by simpa using hx 1
  have hy1 : β (sl2Lower 1) = sl2Lower 1 := by simpa using hy 1
  set f : K → K := fun a =>
    ((β (sl2Upper a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1 with hfdef
  set g : K → K := fun a =>
    ((β (sl2Lower a) : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 with hgdef
  have hf : ∀ a, β (sl2Upper a) = sl2Upper (f a) := by
    intro a
    apply eq_sl2Upper_of_commute
    rw [← hx1, ← map_mul, ← map_mul, ← sl2Upper_add, ← sl2Upper_add, add_comm]
  have hg : ∀ a, β (sl2Lower a) = sl2Lower (g a) := by
    intro a
    apply eq_sl2Lower_of_commute
    rw [← hy1, ← map_mul, ← map_mul, ← sl2Lower_add, ← sl2Lower_add, add_comm]
  have hfadd : ∀ a b, f (a + b) = f a + f b := fun a b => sl2Upper_injective (by
    rw [← hf, sl2Upper_add, map_mul, hf, hf, ← sl2Upper_add])
  have hf0 : f 0 = 0 := sl2Upper_injective (by rw [← hf, sl2Upper_zero, map_one])
  have hg0 : g 0 = 0 := sl2Lower_injective (by rw [← hg, sl2Lower_zero, map_one])
  have hfι : ∀ c, f (ι c) = ι c := fun c => sl2Upper_injective (by rw [← hf, hx])
  have hf1 : f 1 = 1 := by simpa using hfι 1
  have hfinj : Function.Injective f := fun a b h =>
    sl2Upper_injective (β.injective (by rw [hf, hf, h]))
  have hfne : ∀ a : K, a ≠ 0 → f a ≠ 0 := fun a ha h => ha (hfinj (by rw [h, hf0]))
  have hW1 : β (sl2Weyl 1) = sl2Weyl 1 := by
    rw [sl2Weyl, map_mul, map_mul, hx1, inv_one, hy1]
  have hkey : ∀ a : K, a ≠ 0 → f a * g a⁻¹ = 1 := by
    intro a ha
    have h1 := congrArg β (sl2Upper_mul_sl2Lower_inv_pow_three ha)
    rw [map_pow, map_mul, hf, hg, map_one] at h1
    exact mul_eq_one_of_sl2Upper_mul_sl2Lower_pow_three (hfne a ha) h1
  have hgf : ∀ a : K, a ≠ 0 → g a⁻¹ = (f a)⁻¹ := fun a ha => eq_inv_of_mul_eq_one_right (hkey a ha)
  have hDf : ∀ s : Kˣ, β (sl2Diag s) = sl2Diag (Units.mk0 (f s) (hfne s s.ne_zero)) := by
    intro s
    have hWs : β (sl2Weyl (s : K)) = sl2Weyl (f s) := by
      rw [sl2Weyl, map_mul, map_mul, hf, hg, hgf s s.ne_zero, sl2Weyl]
    rw [← sl2Weyl_mul_sl2Weyl_one, map_mul, hWs, hW1, ← sl2Weyl_mul_sl2Weyl_one, Units.val_mk0]
  have hfsq : ∀ a b : K, a ≠ 0 → f (a * a * b) = f a * f a * f b := by
    intro a b ha
    have h1 := congrArg β (sl2Diag_mul_sl2Upper_mul_inv (Units.mk0 a ha) b)
    rw [map_mul, map_mul, map_inv, hDf, hf, hf, sl2Diag_mul_sl2Upper_mul_inv, Units.val_mk0,
      Units.val_mk0] at h1
    exact (sl2Upper_injective h1).symm
  have hfmul : ∀ a b, f (a * b) = f a * f b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, hf0, zero_mul]
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact ha (by rw [hr, mul_zero])
    have h1 := hfsq r b hr0
    have h2 := hfsq r 1 hr0
    rw [mul_one, hf1, mul_one] at h2
    rw [hr, h1, h2]
  let ρh : K →+* K :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul, map_zero' := hf0, map_add' := hfadd }
  have hbij : Function.Bijective ρh := ⟨hfinj, Finite.surjective_of_injective hfinj⟩
  refine ⟨RingEquiv.ofBijective ρh hbij, fun c => hfι c, fun a => ⟨hf a, ?_⟩⟩
  change β (sl2Lower a) = sl2Lower (f a)
  rw [hg]
  congr 1
  by_cases ha : a = 0
  · rw [ha, hg0, hf0]
  · have h1 := hgf a⁻¹ (inv_ne_zero ha)
    rw [inv_inv] at h1
    rw [h1]
    have h2 : f a * f a⁻¹ = 1 := by rw [← hfmul, mul_inv_cancel₀ ha, hf1]
    exact inv_eq_of_mul_eq_one_left h2

end SL2

end CFSG.SeitzReduction.E8Pilot
