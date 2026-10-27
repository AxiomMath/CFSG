module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.ClassicalInvolution.SmallCases.EvenLie.Unitary

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
open CFSG.ComponentClassification.UnbalancingLocal.EvenUnitaryComponents

theorem involutionCentralizersCharTwo_unitaryPSU {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) :
    InvolutionCentralizersCharTwo (unitaryPSU h n) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨e⟩ := nonempty_primeFormP_mulEquiv h hC
  have hconj := conj_injective_primeFormP h hC hn
  have : Finite K := h.finite
  refine InvolutionCentralizersCharTwo.of_mulEquiv e.symm ?_
  intro t ht
  have hα2 : orderOf (MulAut.conj t) = 2 := by
    rw [orderOf_injective _ hconj]
    exact ht
  have hαinn : MulAut.conj t ∈ inner
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    ⟨t, rfl⟩
  have hF : primeFormFieldFactor h hC hn hq (MulAut.conj t) = RingEquiv.refl K := by
    have hαD : MulAut.conj t ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ (MulAut.conj t)).mp hαinn
      exact ⟨_, hs.symm⟩
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker] at hαD
    exact hαD
  obtain ⟨s, hs1, hss, hαs⟩ :=
    (even_unitary_involution_matrix_lifts h hC hn hq (MulAut.conj t) hα2).2.1 hF
  obtain ⟨R, hRX, hnorm, hR, hcent⟩ := exists_two_radical_primeFormConj h hC hn hq le_rfl s hs1 hss
  rw [← hαs] at hRX hnorm hcent
  exact isCharacteristicP_two_centralizer_of_two_radical (MulAut.conj : _ →* _) hconj R hRX hnorm
    hR hcent


theorem involutionCentralizersCharTwo_of_psu_model {X : Type} [Group X] {n f : ℕ}
    (hT : StatedClassicalModel X .PSU n 2 f) : InvolutionCentralizersCharTwo X := by
  obtain ⟨⟨-, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := hT
  have h : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬ (n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  exact InvolutionCentralizersCharTwo.of_mulEquiv (eT.trans (unitaryPSUEquiv h (by omega)).symm)
    (involutionCentralizersCharTwo_unitaryPSU h hn hq')

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
