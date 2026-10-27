module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3OutCore
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.OuterAutomorphisms

theorem threeFilter_primeFormP_three {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : ¬(3 = 3 ∧ p ^ f = 2)) :
    ThreeFilter (inner (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  obtain ⟨-, -, -, -, -, -, -, -, hDn, hinn, -⟩ := unitary_prime_form_full_semilinear_realization
    h (isPrimeFormGram_one (n := 3) (K := K)) (le_refl 3) hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h (le_refl 3) hq
  refine ⟨primeFormD h _, ⊤, hDn, fun α hα => ?_, le_top, fun d hd => ⟨1, ?_⟩,
    fun x _ y _ => OuterDerived.commutator_mem_primeFormD h (le_refl 3) hq x y,
    fun a _ _ => Subgroup.mem_top a⟩
  · obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  · rw [pow_one]
    refine pow_mem_normal_of_relIndex_dvd ?_ hd
    rw [Subgroup.relIndex, Subgroup.index_eq_card, hcard]
    exact Nat.gcd_dvd_left 3 _

end CFSG.LocalAnalysis.RankThreeTheoremC
