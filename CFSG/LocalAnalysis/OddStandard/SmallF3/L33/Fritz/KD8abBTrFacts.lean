module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBTrFacts1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abBTrFacts2

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8
open CFSG.ComponentClassification.HSFLit.Sec8

namespace MB
open CFSG.ComponentClassification.HSFLit.Sec8.MB

theorem all_of_halves {p : ℕ × ℕ} (ha : ((H4Zof p).take 64).all (trCheck p) = true)
    (hb : ((H4Zof p).drop 64).all (trCheck p) = true) : (H4Zof p).all (trCheck p) = true := by
  rw [← List.take_append_drop 64 (H4Zof p), List.all_append, ha, hb, Bool.and_self]

theorem tr_facts : ∀ p ∈ goodIdx, (H4Zof p).all (trCheck p) = true := by
  intro p hp
  simp only [goodIdx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [all_of_halves tr_facts_1a tr_facts_1b, all_of_halves tr_facts_2a tr_facts_2b,
    all_of_halves tr_facts_3a tr_facts_3b, all_of_halves tr_facts_4a tr_facts_4b,
    all_of_halves tr_facts_5a tr_facts_5b, all_of_halves tr_facts_6a tr_facts_6b,
    all_of_halves tr_facts_7a tr_facts_7b, all_of_halves tr_facts_8a tr_facts_8b]

end MB

end Sec8

end CFSG.OddStandard.SmallF3.L33.KD
