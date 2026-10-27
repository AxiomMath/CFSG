module

public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Subgroup

def sqComm (T : Type*) [Group T] : Subgroup T :=
  ⁅(⊤ : Subgroup T), ⊤⁆ ⊔ Subgroup.closure {x | ∃ s : T, x = s ^ 2}

theorem sqComm_characteristic (T : Type*) [Group T] : (sqComm T).Characteristic := by
  refine characteristic_iff_map_le.mpr fun ϕ => ?_
  have hc : (⁅(⊤ : Subgroup T), ⊤⁆ : Subgroup T).Characteristic := inferInstance
  unfold sqComm
  rw [Subgroup.map_sup]
  refine sup_le (le_sup_of_le_left (characteristic_iff_map_le.mp hc ϕ)) ?_
  rw [MonoidHom.map_closure]
  refine le_sup_of_le_right ?_
  rw [closure_le]
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact Subgroup.subset_closure ⟨ϕ s, by simp⟩

theorem mem_sqComm_iff {G : Type*} [Group G] (S : Subgroup G) (x : S) :
    x ∈ sqComm S ↔ (x : G) ∈ ⁅S, S⁆ ⊔ Subgroup.closure {y | ∃ s ∈ S, y = s ^ 2} := by
  have htop : (⊤ : Subgroup S).map S.subtype = S := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have himg : S.subtype '' {x : S | ∃ s : S, x = s ^ 2} = {y | ∃ s ∈ S, y = s ^ 2} := by
    ext y
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, s.2, by simp⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩ ^ 2, ⟨⟨s, hs⟩, rfl⟩, by simp⟩
  have hmap : (sqComm S).map S.subtype
      = ⁅S, S⁆ ⊔ Subgroup.closure {y | ∃ s ∈ S, y = s ^ 2} := by
    rw [sqComm, Subgroup.map_sup, Subgroup.map_commutator, htop, MonoidHom.map_closure, himg]
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem S.subtype_injective).symm

end CFSG.HardMathSupport.RichardWeiss.Proving
