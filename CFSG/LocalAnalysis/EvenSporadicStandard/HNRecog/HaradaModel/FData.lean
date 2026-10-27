module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

@[expose] def fWords : List (List ℕ) :=
  [[5, 4, 7, 5, 3, 7, 6, 3, 5, 6, 2, 3, 6, 1], [7, 1, 3, 7, 1, 7, 2, 5, 6, 5, 7, 2, 6, 5, 1]]

@[expose] def imgA5 : List ↥(alternatingGroup (Fin 5)) :=
  [⟨[0, 2].formPerm * [1, 4].formPerm, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨[0, 3, 1].formPerm, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩]

theorem card_target_A5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
