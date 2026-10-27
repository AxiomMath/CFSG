module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

theorem mcltf_facts_perm {n : ℕ} (hn : 5 ≤ n) : mcltf_Facts (Equiv.Perm (Fin n)) := by
  have h5 : 5 ≤ Nat.card (Fin n) := by rwa [Nat.card_eq_fintype_card, Fintype.card_fin]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hs := alternatingGroup.isSimpleGroup h5
  refine mcltf_facts_of_derived_index_two (alternatingGroup (Fin n)) 1 ?_ hs ?_
    alternatingGroup.index_eq_two
  · rw [derivedSeries_one]
    exact alternatingGroup.commutator_perm_eq h5
  · exact mcltf_exists_ne_of_perfect (commutator_alternatingGroup_eq_top h5)

end CFSG.HardMathSupport.Solomon.Coordinator
