module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiAltCore
import CFSG.GroupTheory.SylowIntersectionControl.AltCore.PartB
import CFSG.GroupTheory.SylowIntersectionControl.IsolatedTransfer

public section

namespace CFSG.GroupTheory

open Equiv Equiv.Perm Subgroup AltCore

private theorem eq_top_or_eq_alternatingGroup {n : ℕ} {X : Subgroup (Perm (Fin n))}
    (hLX : alternatingGroup (Fin n) ≤ X) : X = ⊤ ∨ X = alternatingGroup (Fin n) := by
  by_cases hXL : X ≤ alternatingGroup (Fin n)
  · exact Or.inr (le_antisymm hXL hLX)
  · obtain ⟨g, hgX, hgL⟩ := SetLike.not_le_iff_exists.mp hXL
    refine Or.inl (eq_top_iff.mpr fun h _ => ?_)
    by_cases hhL : h ∈ alternatingGroup (Fin n)
    · exact hLX hhL
    · simpa using mul_mem (hLX (mul_inv_mem_alternatingGroup hhL hgL)) hgX

theorem gomiAltCore_holds : GomiAltCore := by
  intro n hn hn2 X H hLX _ hH hHX hiso
  rcases eq_top_or_eq_alternatingGroup hLX with rfl | rfl
  · rw [inf_top_eq] at hiso ⊢
    obtain ⟨Y, hY, hYa⟩ := exists_goodY_sym hn hn2 hH hiso
    exact ⟨Y, hY.1, hY.2.1, IsPIsolatedOver.exists_le_of_sq_mem hiso hH hYa, hY.2.2⟩
  · obtain ⟨Y, hY, hK⟩ := exists_goodY_alt hn hn2 hH hHX hiso
    exact ⟨Y, hY.1, hY.2.1, hK, hY.2.2⟩

end CFSG.GroupTheory
