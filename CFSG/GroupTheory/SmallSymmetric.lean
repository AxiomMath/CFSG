module

import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open Equiv

theorem eq_or_eq_or_eq_of_fin_three {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (p : Fin 3) : p = i ∨ p = j ∨ p = k := by
  fin_cases p <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

theorem swap_mul_swap_same_inv_apply_fin_three {i j k : Fin 3} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) :
    (swap i j * swap j k : Perm (Fin 3))⁻¹ i = k ∧
      (swap i j * swap j k : Perm (Fin 3))⁻¹ j = i ∧
      (swap i j * swap j k : Perm (Fin 3))⁻¹ k = j ∧
      ((swap i j * swap j k : Perm (Fin 3)) ^ 2)⁻¹ i = j ∧
      ((swap i j * swap j k : Perm (Fin 3)) ^ 2)⁻¹ j = k ∧
      ((swap i j * swap j k : Perm (Fin 3)) ^ 2)⁻¹ k = i := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> decide

theorem isSwap_of_mul_self_eq_one_fin_three (σ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1)
    (h2 : σ * σ = 1) : σ.IsSwap := by
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ = 1 → σ.support.card = 2 := by
    decide
  exact Equiv.Perm.card_support_eq_two.1 (key σ h1 h2)

theorem card_support_eq_four_of_mul_self_eq_one_not_isSwap_fin_four (σ : Equiv.Perm (Fin 4))
    (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : ¬ σ.IsSwap) : σ.support.card = 4 := by
  have hne : σ.support.card ≠ 2 := fun h =>
    h3 (Equiv.Perm.card_support_eq_two.1 h)
  have key : ∀ σ : Equiv.Perm (Fin 4), σ ≠ 1 → σ * σ = 1 → σ.support.card ≠ 2 →
      σ.support.card = 4 := by
    decide
  exact key σ h1 h2 hne

end CFSG.GroupTheory

end
