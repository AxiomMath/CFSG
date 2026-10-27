module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCo3
public import CFSG.Sporadic.SmallOddCore.Co3Aut

public section

namespace CFSG.ComponentClassification.RestrictedStd.Spor

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_small_of_mem_co3Orders {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ center Y) ∈ co3Orders) : ¬ SmallCentralQuotient Y := by
  refine not_small_of_card_quotient ?_
  simp only [co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h <;> rw [h]
  · exact not_isSmallOrder_of_between (q₀ := 142) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  · exact not_isSmallOrder_of_between (q₀ := 57) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)

theorem sporadicCase_Co3 : SporadicCase .Co3 := by
  refine sporadicCase_of_comps (fun G _ _ ⟨e⟩ t ht => ?_) (outer_of_forall_inner fun α => ?_)
  · exact (co3_inner_comps e t ht).mono fun Y _ h => not_small_of_mem_co3Orders h
  · obtain ⟨g, hg⟩ := ctuc_co3_all_automorphisms_inner.{0}.2.1.1 α
    exact ⟨g, hg.symm⟩

end CFSG.ComponentClassification.RestrictedStd.Spor
