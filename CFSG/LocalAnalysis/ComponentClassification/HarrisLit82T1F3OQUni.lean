module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Assembly.LowTwoRank

theorem outNoA4_of_statedClassicalModel_PSU {S : Type} [Group S] {n p f : ℕ}
    (hS : StatedClassicalModel S .PSU n p f) : OutNoA4 S := by
  obtain ⟨-, -, hn, hq⟩ := hS.1
  obtain ⟨⟨K, _, h, ⟨e⟩⟩, -⟩ := unitary_classical_model_outer_normalizer hS
  have hq' : ¬(n = 3 ∧ p ^ f = 2) := fun h32 => hq (Prod.ext h32.1 h32.2)
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨⟨e'⟩, hcyc, -⟩ := unitary_full_diagonal_outer_order h hn hq'
  obtain ⟨-, -, -, -, -, -, -, hker, hDn, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq'
  have : Finite K := h.finite
  have : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  exact OutNoA4.of_mulEquiv (e'.trans e.symm)
    (outNoA4_of_ker_cyclic (primeFormFieldFactor h hC hn hq') mul_comm_of_isCyclic hker.le hcyc)

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
