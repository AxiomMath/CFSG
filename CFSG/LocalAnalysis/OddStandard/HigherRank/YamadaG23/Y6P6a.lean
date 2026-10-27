module

public import TauCeti.GroupTheory.Perm.Recognition

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y6_index_le_four {K : Subgroup (Equiv.Perm (Fin 6))} (h : 180 ≤ Nat.card K) :
    alternatingGroup (Fin 6) ≤ K := by
  have h1 : K.index * Nat.card K = 720 := by
    rw [Subgroup.index_mul_card, Nat.card_perm]
    simp [Nat.factorial]
  refine TauCeti.alternatingGroup_le_of_index_lt (by simp) ?_
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  nlinarith

end CFSG.OddStandard.HigherRank.YamadaG23
