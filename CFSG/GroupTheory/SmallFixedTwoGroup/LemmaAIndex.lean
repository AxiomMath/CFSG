module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

open Subgroup

theorem index_centralizer_le_two {T : Type*} [Group T] {s z : T}
    (h : ∀ g : T, g * s * g⁻¹ = s ∨ g * s * g⁻¹ = z * s) :
    (centralizer ({s} : Set T)).index ≤ 2 := by
  rw [Subgroup.index_centralizer_eq_ncard]
  refine (Set.ncard_le_ncard (t := ({s, z * s} : Set T)) ?_).trans ?_
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    obtain ⟨g, hg⟩ := isConj_iff.mp hy
    rcases h g with hg' | hg'
    · exact Or.inl (hg.symm.trans hg')
    · exact Or.inr (hg.symm.trans hg')
  · have hle := Set.ncard_insert_le s ({z * s} : Set T)
    simpa using hle

end CFSG.GroupTheory.SmallFixedTwoGroup
