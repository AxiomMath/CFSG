module

public import CFSG.GH74.Generic.S45.LAltCaseI
public import CFSG.GH74.Generic.S45.LAltCaseII

public section

namespace CFSG.GH74.Generic.S45.LAlt

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

variable {n : ℕ}

theorem badCent_of_simple {σ : Perm (Fin n)} (hσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    {Lb : Subgroup (Perm (Fin n))} (hLb : Lb ≤ centAlt σ) (hperf : ⁅Lb, Lb⁆ = Lb)
    (hsimple : ∀ N : Subgroup (Perm (Fin n)), N ≤ Lb → (∀ g ∈ Lb, ∀ h ∈ N, g * h * g⁻¹ ∈ N) →
      N = ⊥ ∨ N = Lb)
    {v₀ : Perm (Fin n)} (hv₀ : v₀ ∈ Lb) (hv₀2 : orderOf v₀ = 2) : BadCent σ := by
  have hv₀1 : v₀ ≠ 1 := by
    rintro rfl
    simp at hv₀2
  by_cases hfix : ∀ l ∈ Lb, ∀ x, σ x ≠ x → l x = x
  · exact badCent_of_fixes hσ hσ1 hLb hperf hv₀ hv₀1 hfix
  · push Not at hfix
    obtain ⟨l, hl, x, hx, hlx⟩ := hfix
    exact badCent_of_moves hσ hLb hperf hsimple hv₀ hv₀2 ⟨l, hl, x, hx, hlx⟩

end CFSG.GH74.Generic.S45.LAlt
