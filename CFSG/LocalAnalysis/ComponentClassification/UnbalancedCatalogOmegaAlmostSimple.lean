module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizer

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank

open OmegaRadical in
theorem even_orthogonal_almost_simple_odd_core_vanishing {X : Type} [Group X] [Finite X]
    [IsSimpleGroup (CFSG.generalizedFitting X)]
    (hnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) (t : StatedLieTag)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n f : ℕ}
    (hmodel : StatedClassicalModel (CFSG.generalizedFitting X) t n 2 f) :
    (4 ≤ n ∧ 1 ≤ f) ∧
      ∀ z : X, orderOf z = 2 → CFSG.oddCore ↥(Subgroup.centralizer {z}) = ⊥ := by
  have hfull := even_orthogonal_all_involution_full_centralizer_odd_core
    (CFSG.generalizedFitting X) t ht n f hmodel
  refine ⟨?_, almost_simple_oddCore_of_modelFull hnonab t ht hmodel hfull⟩
  rcases ht with rfl | rfl
  · obtain ⟨-, hf, hn⟩ := hmodel.1
    exact ⟨hn, hf⟩
  · obtain ⟨-, hf, hn⟩ := hmodel.1
    exact ⟨hn, hf⟩

end CFSG.ComponentClassification.UnbalancedCatalog
