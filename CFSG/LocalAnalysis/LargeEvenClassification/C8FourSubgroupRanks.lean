module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroups

public section

namespace CFSG.LargeEvenClassification.Helpers

theorem c8Four_all_rank_cards (i : Fin 896) :
    (c8FourRecordBinaryImages (c8FourRecord i)).card =
      2 ^ (c8FourRecord i).generators.length :=
  c8Four_record_property_of_chunks
    (fun r => (c8FourRecordBinaryImages r).card = 2 ^ r.generators.length)
    c8Four_chunk0_rank_cards
    c8Four_chunk1_rank_cards
    c8Four_chunk2_rank_cards
    c8Four_chunk3_rank_cards
    c8Four_chunk4_rank_cards
    c8Four_chunk5_rank_cards
    c8Four_chunk6_rank_cards
    c8Four_chunk7_rank_cards
    c8Four_chunk8_rank_cards
    c8Four_chunk9_rank_cards
    c8Four_chunk10_rank_cards
    c8Four_chunk11_rank_cards
    c8Four_chunk12_rank_cards
    c8Four_chunk13_rank_cards
    i

theorem c8Four_listed_rank (i : Fin 896) :
    pGeneratorRank 2 (c8FourListedSubgroup i) = (c8FourRecord i).generators.length := by
  apply le_antisymm
  · exact c8FourRecord_generator_rank_le (c8FourRecord i) (c8Four_all_records_valid i)
  · have h := c8FourRecord_rank_lower_bound (c8FourRecord i) (c8Four_all_records_valid i)
    rw [c8Four_all_rank_cards, Nat.log_pow (by decide : 1 < 2)] at h
    exact h

end CFSG.LargeEvenClassification.Helpers
