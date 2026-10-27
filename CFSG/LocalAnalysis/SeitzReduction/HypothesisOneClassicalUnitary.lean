module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryShear
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryLagrangian
import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalUnitaryOuter
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAllInvolutions
import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow

public section

namespace CFSG.SeitzReduction

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.ComponentClassification.UnbalancedCatalog
  (even_unitary_all_involution_full_centralizer_odd_core)
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents
  (conj_injective_primeFormP)
open CFSG.ComponentClassification.OutcomeLocal (primeFormOneEquiv)

variable {f n : ℕ} {K : Type} [Field K]

theorem even_of_range_eq_ker (N : Matrix (Fin n) (Fin n) K)
    (hN : LinearMap.range N.mulVecLin = LinearMap.ker N.mulVecLin) : Even n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun, hN] at hrn
  exact ⟨_, hrn.symm⟩

theorem involutionCriterion_primeFormP (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 5 ≤ n)
    (α : MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))) (hα : orderOf α = 2) :
    InvolutionCriterion α := by
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  obtain ⟨hF, hinn, -, -⟩ := even_unitary_involution_matrix_lifts h hC hn3 hq α hα
  rcases hF with hF | hF
  · obtain ⟨s, hs1, hs2, rfl⟩ := hinn hF
    by_cases hWL : LinearMap.range (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin =
        LinearMap.ker (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1).mulVecLin
    · obtain ⟨m, hm⟩ := even_of_range_eq_ker _ hWL
      exact UnitaryLagrangian.involutionCriterion_primeFormConj_of_eq h (by omega) hC s hs2 hWL
    · exact involutionCriterion_primeFormConj_of_ne h hC (by omega) s hs2 hs1 hWL
  · exact UnitaryOuter.involutionCriterion_of_fieldFactor_bar h hn3 hq (by omega) hC α hα hF

theorem hypothesisOne_primeFormP (h : UnitaryFieldData 2 f K) {C : GL (Fin n) K}
    (hC : IsPrimeFormGram C) (hn : 5 ≤ n) :
    HypothesisOne (primeFormP h (C : Matrix (Fin n) (Fin n) K)) := by
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => by omega
  exact hypothesisOne_of_involutionCriterion (conj_injective_primeFormP h hC hn3)
    (fun _ hH => even_unitary_all_involution_full_centralizer_odd_core h hC hn3 hq hH)
    (fun x hx => involutionCriterion_primeFormP h hC hn x hx)

theorem hypothesisOne_unitaryPSU (h : UnitaryFieldData 2 f K) (hn : 5 ≤ n) :
    HypothesisOne (unitaryPSU h n) :=
  CFSG.EvenSmallLie.hypothesisOne_of_mulEquiv (primeFormOneEquiv h n)
    (hypothesisOne_primeFormP h isPrimeFormGram_one hn)

end CFSG.SeitzReduction
