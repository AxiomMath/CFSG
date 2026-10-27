module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713SCatalog
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder
public import CFSG.LocalAnalysis.GL83PartI.I713.UnitaryDiag

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S

open CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem outLift_primeFormP_one {ℓ p f n : ℕ} (hℓ : ℓ.Prime) {K : Type} [Field K]
    (hU : UnitaryFieldData p f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ p ^ f = 2))
    (hdiag : ¬ ℓ ∣ Nat.gcd n (p ^ f + 1))
    [Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))] :
    OutLift ℓ (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  haveI := hU.finite
  obtain ⟨-, -, -, -, -, h6, -, hker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU hC hn hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU hn hq
  refine outLift_of_section hℓ (primeFormFieldFactor hU hC hn hq) (primeFormFieldHom hU hC)
    (fun σ => ?_) ?_ ?_
  · have := h6 1 σ
    rwa [map_one, one_mul] at this
  · rw [hker]
    intro α hα
    obtain ⟨s, hs⟩ := (hinn α).1 hα
    exact ⟨_, hs.symm⟩
  · rw [hker]
    show ¬ ℓ ∣ Nat.card _
    rw [hcard]
    exact hdiag

theorem liftClause_classical_PSU {n p f : ℕ} :
    FamilyLift fun S _ => StatedClassicalModel S .PSU n p f := by
  intro S _ _ _ hnonab h ℓ hℓ hℓ2 hSℓ
  obtain ⟨⟨hp, hf, hn, hq⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq' : ¬ (n = 3 ∧ p ^ f = 2) := fun ⟨h1, h2⟩ => hq (by rw [h1, h2])
  by_cases hdvd : ℓ ∣ Nat.gcd n (p ^ f + 1)
  · exfalso
    obtain ⟨hℓn, hℓq⟩ := Nat.dvd_gcd_iff.1 hdvd
    have h2 := GL83.I713.two_le_pRank_statedPSU_of_dvd hK hℓ hℓ2 hn hℓn hℓq
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hℓ.one_lt eT] at h2
    omega
  · obtain ⟨⟨eR⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
      (isPrimeFormGram_one (n := n)) hn hq'
    let e : S ≃* primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      (eT.trans (unitaryPSUEquiv hU (by omega)).symm).trans eR.symm
    haveI : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      Finite.of_equiv S e.toEquiv
    exact OutLift.of_mulEquiv e (outLift_primeFormP_one hℓ hU hn hq' hdvd)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K713S
