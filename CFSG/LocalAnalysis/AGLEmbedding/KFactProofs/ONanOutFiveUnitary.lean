module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveSeries
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.AGLEmbedding.OutFive

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms

theorem outPlaneSeries_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    {n : ℕ} (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) :
    OutPlaneSeries p (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, hcyc, -, -⟩ := unitary_full_diagonal_outer_order h hn hq
  have hring := card_ringAut_and_isCyclic h.prime K h.card
  have : IsCyclic (RingAut K) := hring.2
  refine ⟨primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), hFker ▸ inferInstance,
    ?_, ?_⟩
  · intro R hRD hR hcard hRI
    have := hcyc
    exact false_of_plane_in_cyclic_quotient hp hRD hR hcard hRI
  · intro R hR hcard hRD
    exact false_of_plane_meets_kernel_trivially hp (primeFormFieldFactor h hC hn hq) hR hcard
      (hFker ▸ hRD)

theorem outPlaneSeries_PSU_model {p : ℕ} (hp : p.Prime) {X : Type} [Group X] {n r m : ℕ}
    (h : StatedClassicalModel X .PSU n r m) : OutPlaneSeries p X := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : UnitaryFieldData r m K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ r ^ m = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  have e' : X ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  exact OutPlaneSeries.of_mulEquiv e' (outPlaneSeries_primeFormP hU hn3 hq hp)

end CFSG.AGLEmbedding.OutFive
