module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem fourB_card_shape2222 :
    Nat.card {s : alternatingGroup (Fin 8) // (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2}} =
      105 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, AlternatingGroup.card_of_cycleType,
    if_pos (by decide)]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
