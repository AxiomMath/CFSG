module

public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG

variable {G H : Type*} [Group G] [Group H]

theorem centralizer_singleton_map (e : G ≃* H) (t : G) :
    (Subgroup.centralizer ({t} : Set G)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set H) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg e h
  · intro h
    simpa using congrArg e.symm h

theorem centralizer_inter_map (e : G ≃* H) (N : Subgroup G) (t : G) :
    (N ⊓ Subgroup.centralizer ({t} : Set G)).map e.toMonoidHom =
      N.map e.toMonoidHom ⊓ Subgroup.centralizer ({e t} : Set H) := by
  rw [Subgroup.map_inf _ _ _ e.injective, centralizer_singleton_map]

end CFSG
