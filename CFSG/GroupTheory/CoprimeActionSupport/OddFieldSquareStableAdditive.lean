module

import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring.RingNF


public section

namespace CFSG.GroupTheory.CoprimeActionSupport.OddFieldSquareStableAdditive

theorem eq_top_of_sq_stable {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (A : AddSubgroup F)
    (hA : ∀ (a : Fˣ) (x : F), x ∈ A → ((a : F) ^ 2) * x ∈ A) (hne : A ≠ ⊥) : A = ⊤ := by
  have exists_sq_sub_sq {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (t : F) :
      ∃ u v : F, t = u ^ 2 - v ^ 2 :=
    ⟨(t + 1) / 2, (t - 1) / 2, by field_simp; ring⟩
  have mul_mem_of_sq_stable {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (A : AddSubgroup F)
      (hA : ∀ (a : Fˣ) (x : F), x ∈ A → ((a : F) ^ 2) * x ∈ A) (t x : F) (hx : x ∈ A) :
      t * x ∈ A := by
    obtain ⟨u, v, rfl⟩ := exists_sq_sub_sq h2 t
    have key : ∀ w : F, w ^ 2 * x ∈ A := by
      intro w
      by_cases hw : w = 0
      · simp [hw]
      · simpa using hA (Units.mk0 w hw) x hx
    rw [sub_mul]
    exact A.sub_mem (key u) (key v)
  obtain ⟨⟨x, hxA⟩, hx0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero (H := A)).mp hne
  have hx0 : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [eq_top_iff]
  intro y _
  have := mul_mem_of_sq_stable h2 A hA (y / x) x hxA
  rwa [div_mul_cancel₀ _ hx0] at this

end CFSG.GroupTheory.CoprimeActionSupport.OddFieldSquareStableAdditive
