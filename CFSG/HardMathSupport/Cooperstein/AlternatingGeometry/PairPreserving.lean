module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

variable {Ω : Type*} [DecidableEq Ω] {σ : Perm Ω}

theorem pair_cases {g : Perm Ω} (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (hg : ∀ z, g z = z ∨ g z = σ z) (x : Ω) :
    (g x = x ∧ g (σ x) = σ x) ∨ (g x = σ x ∧ g (σ x) = x) := by
  rcases hg x with h | h
  · left
    refine ⟨h, ?_⟩
    rcases hg (σ x) with h' | h'
    · exact h'
    · exfalso
      rw [hσ2] at h'
      exact hσ1 x (g.injective (h'.trans h.symm))
  · right
    refine ⟨h, ?_⟩
    rcases hg (σ x) with h' | h'
    · exfalso
      exact hσ1 x (g.injective (h'.trans h.symm))
    · rw [h', hσ2]

theorem sq_eq_one_of_pair {g : Perm Ω} (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x)
    (hg : ∀ z, g z = z ∨ g z = σ z) : g * g = 1 := by
  ext x
  rcases pair_cases hσ1 hσ2 hg x with ⟨h1, -⟩ | ⟨h1, h2⟩
  · simp [Perm.mul_apply, h1]
  · simp [Perm.mul_apply, h1, h2]

@[expose] def pairPres (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) :
    Subgroup (Perm Ω) where
  carrier := {g | ∀ z, g z = z ∨ g z = σ z}
  mul_mem' := by
    intro g h hg hh z
    simp only [Perm.mul_apply]
    rcases hh z with e | e
    · rw [e]; exact hg z
    · rw [e]
      rcases pair_cases hσ1 hσ2 hg z with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · right; exact e2
      · left; exact e2
  one_mem' := fun z => Or.inl rfl
  inv_mem' := by
    intro g hg z
    have h1 : g⁻¹ = g := by
      have := sq_eq_one_of_pair hσ1 hσ2 hg
      exact inv_eq_of_mul_eq_one_right this
    rw [h1]; exact hg z

theorem mem_pairPres {hσ1 : ∀ x, σ x ≠ x} {hσ2 : ∀ x, σ (σ x) = x} {g : Perm Ω} :
    g ∈ pairPres σ hσ1 hσ2 ↔ ∀ z, g z = z ∨ g z = σ z := Iff.rfl

theorem swap_mem_pairPres (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (x : Ω) :
    swap x (σ x) ∈ pairPres σ hσ1 hσ2 := by
  intro z
  by_cases h1 : z = x
  · rw [h1, swap_apply_left]; exact Or.inr rfl
  by_cases h2 : z = σ x
  · rw [h2, swap_apply_right, hσ2]; exact Or.inr rfl
  · rw [swap_apply_of_ne_of_ne h1 h2]; exact Or.inl rfl

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
