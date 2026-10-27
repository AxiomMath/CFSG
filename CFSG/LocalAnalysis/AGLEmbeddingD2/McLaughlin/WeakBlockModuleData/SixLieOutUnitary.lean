module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OutL5Proof
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem card_outer_projSU_eq (n p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ p ^ f = 2)) :
    Nat.card (Outer (projSU n p f)) = 2 * f * Nat.gcd n (p ^ f + 1) := by
  have hU := unitaryFieldData_galoisField p f hf
  have hC : IsPrimeFormGram (1 : GL (Fin n) (GaloisField p (2 * f))) := isPrimeFormGram_one_GL
  obtain ⟨⟨e₃⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU hC hn hq
  have e : projSU n p f ≃* primeFormP hU
      ((1 : GL (Fin n) (GaloisField p (2 * f))) : Matrix (Fin n) (Fin n) _) :=
    (projSUEquivStatedProj n p f).trans ((unitaryPSUEquiv hU (by omega)).symm.trans e₃.symm)
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact (unitary_full_diagonal_outer_order hU hn hq).2.2.2.1

theorem not_three_dvd_card_outer_projSU_two_one {n : ℕ} (hn : 4 ≤ n) (hn5 : n ≤ 5) :
    ¬ 3 ∣ Nat.card (Outer (projSU n 2 1)) := by
  rw [card_outer_projSU_eq n 2 1 le_rfl (by omega) (by omega)]
  interval_cases n <;> norm_num

theorem autThreePowInner_psu_two {X : Type} [Group X] {n : ℕ} (hn : 4 ≤ n) (hn5 : n ≤ 5)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU n 2 1) : AutThreePowInner X := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel h
  exact autThreePowInner_of_mulEquiv e
    (autThreePowInner_of_not_three_dvd_outer (not_three_dvd_card_outer_projSU_two_one hn hn5))

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
