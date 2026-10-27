module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelDefs
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelExc

public section

namespace CFSG.EvenSmallLie.Child3.SelExc

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem excludedLie_of_mem_chevalleyExceptionalTags {t : StatedLieTag} {n p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) : ExcludedLie t n p f := by
  intro Y _ _ D a J h hD
  have := h.normal
  exact false_of_lieModel_of_mem_chevalleyExceptionalTags h.centralizer_eq h.orderOf_eq h.le
    h.le_centralizer h.sup_eq h.gl3 ht hD

theorem exceptionalExclusions : ExceptionalExclusions :=
  ⟨excludedLie_of_mem_chevalleyExceptionalTags (by decide),
    excludedLie_of_mem_chevalleyExceptionalTags (by decide),
    excludedLie_of_mem_chevalleyExceptionalTags (by decide),
    excludedLie_of_mem_chevalleyExceptionalTags (by decide),
    excludedLie_of_mem_chevalleyExceptionalTags (by decide)⟩

end CFSG.EvenSmallLie.Child3.SelExc
