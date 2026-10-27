module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic

public section

theorem CFSG.Algebra.addSubgroup_eq_bot_or_eq_top_of_mul_mem {K : Type*} [Field K]
    (S : AddSubgroup K) (hS : ∀ c : K, c ≠ 0 → ∀ x ∈ S, c * x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 0
    · rw [hy]
      exact S.zero_mem
    · have hne : ∃ x ∈ S, x ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hbot ((AddSubgroup.eq_bot_iff_forall S).mpr hcon)
      obtain ⟨x, hxS, hx0⟩ := hne
      have h := hS (y / x) (div_ne_zero hy hx0) x hxS
      rwa [div_mul_cancel₀ y hx0] at h
