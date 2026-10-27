module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec8s_mem_sup_zpowers {t : G} {E : Subgroup G} (ht2 : t * t = 1)
    (htn : ∀ e ∈ E, t * e * t⁻¹ ∈ E) {y : G} (hy : y ∈ zpowers t ⊔ E) :
    y ∈ E ∨ ∃ e ∈ E, y = t * e := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcancel : ∀ a : G, t * (t * a) = a := fun a => by rw [← mul_assoc, ht2, one_mul]
  let T : Subgroup G :=
    { carrier := {y | y ∈ E ∨ ∃ e ∈ E, y = t * e}
      mul_mem' := by
        rintro a b (ha | ⟨e₁, he₁, rfl⟩) (hb | ⟨e₂, he₂, rfl⟩)
        · exact Or.inl (E.mul_mem ha hb)
        · refine Or.inr ⟨(t * a * t⁻¹) * e₂, E.mul_mem (htn a ha) he₂, ?_⟩
          rw [hti]
          calc a * (t * e₂) = t * (t * a) * (t * e₂) := by rw [hcancel]
            _ = t * (t * a * t * e₂) := by group
        · exact Or.inr ⟨e₁ * b, E.mul_mem he₁ hb, by group⟩
        · refine Or.inl ?_
          have e : t * e₁ * (t * e₂) = (t * e₁ * t⁻¹) * (t * t) * e₂ := by group
          rw [e, ht2, mul_one]
          exact E.mul_mem (htn e₁ he₁) he₂
      one_mem' := Or.inl E.one_mem
      inv_mem' := by
        rintro a (ha | ⟨e, he, rfl⟩)
        · exact Or.inl (E.inv_mem ha)
        · refine Or.inr ⟨t * e⁻¹ * t⁻¹, htn _ (E.inv_mem he), ?_⟩
          rw [mul_inv_rev, hti]
          calc e⁻¹ * t = t * (t * e⁻¹) * t := by rw [hcancel]
            _ = t * (t * e⁻¹ * t) := by group }
  have hle : zpowers t ⊔ E ≤ T := by
    refine sup_le ?_ (fun e he => Or.inl he)
    rw [zpowers_le]
    exact Or.inr ⟨1, E.one_mem, by simp⟩
  exact hle hy

end CFSG.OddStandard.SmallF3.Omega
