module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutTowerLinear
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedUnitary

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower

open CFSG.AGLEmbedding CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem outTowerAt_primeFormP {ℓ f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    {N : ℕ} (hN : 3 ≤ N) (hq : ¬(N = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (htot : ¬ p ∣ Nat.totient (Nat.gcd N (ℓ ^ f + 1))) :
    OutTowerAt (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) p := by
  have : Finite K := hU.finite
  obtain ⟨-, -, -, -, -, -, -, -, hDn, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU (isPrimeFormGram_one (n := N)) hN hq
  obtain ⟨-, hcyc, hcard, -⟩ := unitary_full_diagonal_outer_order hU hN hq
  have : ((MulAut.conj : primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) →*
      MulAut (primeFormP hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K))).range).Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  refine ⟨primeFormD hU ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K),
    fun γ α _ => OuterDerived.commutator_mem_primeFormD hU hN hq γ α,
    fun α ⟨k, hk⟩ δ hδ => ?_⟩
  refine commutator_mem_of_isCyclic_quotient hcyc hp ?_ hk hδ
  rw [hcard]
  exact htot

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower
