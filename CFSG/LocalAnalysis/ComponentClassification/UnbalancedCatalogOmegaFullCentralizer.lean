module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaAllInvolution

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank

open OmegaRadical in
theorem even_orthogonal_all_involution_full_centralizer_odd_core (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) : EvenOrthogonalModelFullCentralizer G t n f := by
  have hall := even_orthogonal_all_involution_semilinear_odd_core G t ht n f h
  rcases ht with rfl | rfl
  · intro K _ _ hK e
    obtain ⟨hsemi, hfull⟩ := hall K hK e
    rcases Nat.lt_or_ge n 5 with hlt | hge
    · obtain rfl : n = 4 := by
        have := h.1.2.2
        omega
      exact fullInvolutionOddCore_plus_four G h K hK e hsemi
    · exact hfull hge
  · intro hn K _ _ hK b c hirr e
    exact (hall hn K hK b c hirr e).2

end CFSG.ComponentClassification.UnbalancedCatalog
