module

public import CFSG.CGT.L5R.RelData
public import CFSG.GroupTheory.GL52.InvolutionsConj

public section

namespace CFSG.CGT.L5R

open CFSG.GroupTheory.GL52

@[expose] def tLM : Fin 4 → M5 :=
  ![!![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 1, 0, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 1],
    !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 1, 1]]

theorem l52M_six_add (j : Fin 4) : l52M ⟨6 + j.val, by omega⟩ = tLM j := by
  fin_cases j <;> rfl

@[expose] def upsM : M5 :=
  !![1, 0, 1, 0, 0; 0, 1, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def upsL : G52 :=
  mk5 upsM upsM (by decide)

@[expose] def swapM : M5 :=
  !![0, 0, 0, 0, 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 1, 0, 0, 0, 0]

@[expose] def swapGL : G52 :=
  mk5 swapM swapM (by decide)

@[expose] def cycM : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0]

@[expose] def cycInvM : M5 :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1; 0, 0, 1, 0, 0]

@[expose] def cycL : G52 :=
  mk5 cycM cycInvM (by decide)

theorem swapGL_conj_tL {τ : G52} (hτ : (τ : M5) = tLM 0) : swapGL * τ * swapGL⁻¹ = invT0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hτ]
  simp only [swapGL, invT0, coe_mk5, coe_mk5_inv]
  decide

theorem cycL_conj_upsL : cycL * upsL * cycL⁻¹ = invU0 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  simp only [cycL, upsL, invU0, coe_mk5, coe_mk5_inv]
  decide

theorem upsL_sq : upsL ^ 2 = 1 := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, upsL, coe_mk5, Units.val_one]
  decide

theorem tLM_zero_ne_one : tLM 0 ≠ 1 := by
  decide

theorem exists_conj_tL_or_upsL {β : G52} (hβ : β ^ 2 = 1) (hβ1 : β ≠ 1) {τ : G52}
    (hτ : (τ : M5) = tLM 0) :
    (∃ c : G52, c * τ * c⁻¹ = β) ∨ ∃ c : G52, c * upsL * c⁻¹ = β := by
  rcases inv_commDim_eq_one_or_two hβ hβ1 with h1 | h2
  · obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_t0 hβ h1)
    refine Or.inl ⟨c * swapGL, ?_⟩
    rw [← hc, ← swapGL_conj_tL hτ]
    group
  · obtain ⟨c, hc⟩ := isConj_iff.1 (inv_isConj_u0 hβ h2)
    refine Or.inr ⟨c * cycL, ?_⟩
    rw [← hc, ← cycL_conj_upsL]
    group

theorem upsL_conj_tL {τ : Fin 4 → G52} (hτ : ∀ j, (τ j : M5) = tLM j) :
    upsL * τ 0 * upsL⁻¹ = τ 0 * τ 2 ∧ upsL * τ 1 * upsL⁻¹ = τ 1 * τ 3 ∧
      upsL * τ 2 * upsL⁻¹ = τ 2 ∧ upsL * τ 3 * upsL⁻¹ = τ 3 := by
  refine ⟨Units.ext ?_, Units.ext ?_, Units.ext ?_, Units.ext ?_⟩ <;>
    simp only [Units.val_mul, hτ, upsL, coe_mk5, coe_mk5_inv] <;> decide

theorem tL_mul_upsL_ne {τ : Fin 4 → G52} (hτ : ∀ j, (τ j : M5) = tLM j) :
    τ 0 * upsL ≠ upsL * τ 0 ∧ τ 1 * upsL ≠ upsL * τ 1 ∧
      τ 0 * τ 1 * upsL ≠ upsL * (τ 0 * τ 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
  · have h' := congrArg (fun u : G52 => (u : M5)) h
    simp only [Units.val_mul, hτ, upsL, coe_mk5] at h'
    revert h'
    decide

end CFSG.CGT.L5R
