module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

@[expose] def gradNode : (τ : Tag) → Fin τ.rank
  | .G2 => ⟨0, by decide⟩
  | .F4 => ⟨0, by decide⟩
  | .D4 => ⟨0, by decide⟩
  | .E6 => ⟨1, by decide⟩
  | .E7 => ⟨0, by decide⟩
  | .E8 => ⟨7, by decide⟩

@[expose] def hiRoot : (τ : Tag) → Fin τ.rank → ℤ
  | .G2 => 0
  | .F4 => ![2, 3, 4, 2]
  | .D4 => 0
  | .E6 => ![1, 2, 2, 3, 2, 1]
  | .E7 => ![2, 2, 3, 4, 3, 2, 1]
  | .E8 => ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def lvl (τ : Tag) (γ : Fin τ.rank → ℤ) : ℤ := γ (gradNode τ)

@[expose] def delta1 (τ : Tag) : Fin τ.rank → ℤ := Pi.single (gradNode τ) 1

@[expose] def delta2 (τ : Tag) : Fin τ.rank → ℤ := hiRoot τ - Pi.single (gradNode τ) 1

section Facts

variable {τ : Tag}

theorem hiRoot_mem (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : hiRoot τ ∈ rootFinset τ := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem hiRoot_isMax (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : IsMaxHeightRoot τ (hiRoot τ) := by
  refine ⟨mem_rootFinset.1 (hiRoot_mem hτ), fun γ hγ => ?_⟩
  have key : ∀ γ ∈ rootFinset τ, height γ ≤ height (hiRoot τ) := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact key γ (mem_rootFinset.2 hγ)

theorem lvl_hiRoot (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : lvl τ (hiRoot τ) = 2 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

theorem lvl_bound (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : -2 ≤ lvl τ γ ∧ lvl τ γ ≤ 2 := by
  have key : ∀ γ ∈ rootFinset τ, -2 ≤ lvl τ γ ∧ lvl τ γ ≤ 2 := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact key γ (mem_rootFinset.2 hγ)

theorem eq_hiRoot_of_lvl_eq_two (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (h : lvl τ γ = 2) : γ = hiRoot τ := by
  have key : ∀ γ ∈ rootFinset τ, lvl τ γ = 2 → γ = hiRoot τ := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact key γ (mem_rootFinset.2 hγ) h

theorem not_isRoot_add_hiRoot_of_lvl_nonneg (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (h : 0 < lvl τ γ) : ¬ IsRoot τ (γ + hiRoot τ) := by
  intro hr
  have h1 := (lvl_bound hτ hr).2
  have h2 : lvl τ (γ + hiRoot τ) = lvl τ γ + 2 := by simp [lvl, lvl_hiRoot hτ, Pi.add_apply] <;>
    first | rfl | (have := lvl_hiRoot hτ; simp [lvl] at this ⊢; omega)
  omega

theorem isRoot_delta1 (τ : Tag) : IsRoot τ (delta1 τ) := isRoot_single τ (gradNode τ)

theorem lvl_delta1 (τ : Tag) : lvl τ (delta1 τ) = 1 := by
  simp [lvl, delta1]

theorem isRoot_delta2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : IsRoot τ (delta2 τ) := by
  have key : delta2 τ ∈ rootFinset τ := by
    rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel
  exact mem_rootFinset.1 key

theorem lvl_delta2 (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : lvl τ (delta2 τ) = 1 := by
  rcases hτ with rfl | rfl | rfl | rfl <;> decide +kernel

end Facts

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
