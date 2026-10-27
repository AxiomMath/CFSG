module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.PLSpFourPerm

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] (S : Subgroup G) (Φ : ↥S ≃* Perm (Fin 6))

theorem map_commutator_top_eq :
    Subgroup.map Φ.toMonoidHom ⁅(⊤ : Subgroup ↥S), ⊤⁆ = alternatingGroup (Fin 6) := by
  rw [Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 Φ.surjective,
    ← commutator_def]
  exact alternatingGroup.commutator_perm_eq (by simp)

theorem map_subtype_commutator_top :
    Subgroup.map S.subtype ⁅(⊤ : Subgroup ↥S), ⊤⁆ = ⁅S, S⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem nonempty_commutator_inf_centralizer_equiv (t : G) (ht : t ∈ S) :
    Nonempty (↥(⁅S, S⁆ ⊓ centralizer {t}) ≃*
      ↥(alternatingGroup (Fin 6) ⊓ centralizer {Φ ⟨t, ht⟩})) := by
  obtain ⟨e1⟩ := nonempty_inf_centralizer_equiv_of_injective S.subtype S.subtype_injective
    (⁅(⊤ : Subgroup ↥S), ⊤⁆) ⁅S, S⁆ (map_subtype_commutator_top S) ⟨t, ht⟩
  obtain ⟨e2⟩ := nonempty_inf_centralizer_equiv Φ (⁅(⊤ : Subgroup ↥S), ⊤⁆) _
    (map_commutator_top_eq S Φ) ⟨t, ht⟩
  exact ⟨e1.symm.trans e2⟩

theorem mem_commutator_of_map_mem (x : ↥S) (hx : Φ x ∈ alternatingGroup (Fin 6)) :
    (x : G) ∈ ⁅S, S⁆ := by
  rw [← map_subtype_commutator_top]
  refine ⟨x, ?_, rfl⟩
  rw [← map_commutator_top_eq S Φ] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Φ.injective hyx
  exact this ▸ hy

theorem sign_eq_neg_one_of_notMem_commutator (t : G) (ht : t ∈ S) (hn : t ∉ ⁅S, S⁆) :
    sign (Φ ⟨t, ht⟩) = -1 := by
  rcases Int.units_eq_one_or (sign (Φ ⟨t, ht⟩)) with h | h
  · exact absurd (mem_commutator_of_map_mem S Φ ⟨t, ht⟩ (mem_alternatingGroup.mpr h)) hn
  · exact h

end CFSG.HardMathSupport.Curtis.UnitaryLevi
