module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Tactic.Group

public section

namespace GL83

open scoped Pointwise

theorem I_32_8_proved :
    ∀ (G : Type) [Group G] [IsSimpleGroup G] (A B C : Subgroup G),
      A ≠ ⊤ → B ≠ ⊤ → C ≠ ⊥ → C ≤ A → B ≤ Subgroup.normalizer (C : Set G) →
        (A : Set G) * (B : Set G) ≠ Set.univ := by
  intro G _ _ A B C hA _hB hC hCA hBC hAB
  apply hA
  have hN : Subgroup.normalClosure (C : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure (C : Set G))
      with h1 | h1
    · exact absurd (le_bot_iff.1 (h1 ▸ Subgroup.subset_normalClosure)) hC
    · exact h1
  have hle : Subgroup.normalClosure (C : Set G) ≤ A := by
    refine (Subgroup.closure_le A).2 ?_
    intro z hz
    obtain ⟨y, hy, hc⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    obtain ⟨g, rfl⟩ := isConj_iff.1 hc
    have hg : g ∈ (A : Set G) * (B : Set G) := by
      rw [hAB]
      exact Set.mem_univ g
    obtain ⟨a, ha, c, hc', e⟩ := hg
    have e' : g = a * c := e.symm
    subst e'
    have h1 : c * y * c⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hBC hc') y).1 hy
    have h2 : a * (c * y * c⁻¹) * a⁻¹ ∈ A :=
      A.mul_mem (A.mul_mem ha (hCA h1)) (A.inv_mem ha)
    have h3 : a * c * y * (a * c)⁻¹ = a * (c * y * c⁻¹) * a⁻¹ := by group
    rw [h3]
    exact h2
  rw [hN] at hle
  exact top_le_iff.1 hle

end GL83
