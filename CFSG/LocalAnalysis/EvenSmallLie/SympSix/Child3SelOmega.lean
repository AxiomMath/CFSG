module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOmegaE3
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelStar
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.UnbalancingLocal
  (even_orthogonal_involution_centralizers_component_free)

theorem excluded_POmega_two {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus)
    (n : ℕ) : ExcludedLie t n 2 1 := by
  intro Y _ _ D a J h hL
  have hT : StatedClassicalModel D t n 2 1 := by
    rcases hL with ⟨-, hc⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩ | ⟨-, hm, -⟩
    · exact hc
    all_goals rcases ht with rfl | rfl <;> exact absurd hm (by decide)
  have hn : 4 ≤ n := by
    rcases ht with rfl | rfl
    · exact hT.1.2.2
    · exact hT.1.2.2
  by_cases ha : a ∈ D
  · obtain ⟨u, hu, B, hB⟩ := h.exists_component_of_mem ha (MulEquiv.refl D)
    exact even_orthogonal_involution_centralizers_component_free ht hn le_rfl hT u hu B hB
  · refine ha (h.mem_of_e3 (MulEquiv.refl D) fun x hx => ?_)
    obtain ⟨u, hu, hc⟩ := SelOmega.exists_orderOf_eq_two_commute_of_POmega ht hT x hx
    rw [← hu]
    exact Subgroup.orderOf_dvd_natCard _ (mem_centralizer_singleton_iff.mpr hc.eq)

theorem orthogonalExclusions : OrthogonalExclusions :=
  ⟨excluded_POmega_two (Or.inl rfl) 4, excluded_POmega_two (Or.inl rfl) 5,
    excluded_POmega_two (Or.inl rfl) 6, excluded_POmega_two (Or.inl rfl) 7,
    excluded_POmega_two (Or.inr rfl) 4, excluded_POmega_two (Or.inr rfl) 5,
    excluded_POmega_two (Or.inr rfl) 6⟩

end CFSG.EvenSmallLie.Child3
