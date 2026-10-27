module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc

section Gen

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem transitive_of_twin_nbr_of_not_two (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n)
    (hS : Q8Section X Φ) {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ)
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A')
    (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (hnot : ¬ ∀ M ∈ Φ, M = A ∨ M = A') :
    ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A = M) → M = A' := by
    intro M hM hnot'
    have hMA : M ≠ A := fun h => hnot' ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A hA M hM hnot'))
  have hcA' : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A' = M) → M = A := by
    intro M hM hnot'
    have hMA : M ≠ A' := fun h => hnot' ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A' hA' M hM hnot'))
  have hAA' : ∃ g : X, conjSub g A = A' := by
    by_contra hnc
    apply hnot
    intro M hM
    by_cases hM1 : ∃ g : X, conjSub g A = M
    · left
      obtain ⟨g, hg⟩ := hM1
      refine hcA' M hM ?_
      rintro ⟨g', hg'⟩
      exact hnc ⟨g'⁻¹ * g, by rw [conjSub_mul, hg, ← hg', conjSub_inv_conjSub]⟩
    · right
      exact hcA M hM hM1
  have hcl : ∀ M ∈ Φ, ∃ g : X, conjSub g A = M := by
    intro M hM
    by_cases h : ∃ g : X, conjSub g A = M
    · exact h
    · obtain ⟨g, hg⟩ := hAA'
      exact ⟨g, hg.trans (hcA M hM h).symm⟩
  intro K hK L hL
  obtain ⟨x, hx⟩ := hcl K hK
  obtain ⟨y, hy⟩ := hcl L hL
  exact ⟨y * x⁻¹, by rw [conjSub_mul, ← hx, conjSub_inv_conjSub, hy]⟩

end Gen

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
