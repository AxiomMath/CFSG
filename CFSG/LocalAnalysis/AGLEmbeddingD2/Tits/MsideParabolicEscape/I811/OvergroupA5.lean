module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

theorem kFactOvergroupA5 : KFactOvergroupA5 := by
  intro K _ _ ⟨e⟩ hK _ A W _ _ hW _
  have h60 : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (alternatingGroup (Fin 5)) = 60
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [S3AmalgamBound.OvergroupA5.eq_top_of_not_isPSolvable_three h60 W hW, Subgroup.index_top]
  exact odd_one

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
