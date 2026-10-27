module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthMain
public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic

variable {p e : ℕ} [Fact p.Prime]

private theorem e189_commutator_eq_of_le {G : Type} [Group G] {R : Subgroup G}
    (h : R ≤ ⁅R, R⁆) : ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem e189ModelAt_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) : E189ModelAt p e .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  show E189AtFam (spinGroup (quadOdd n (GaloisField p e)))
    (fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p e)))
  refine e189AtFam_spin_of_ne8 hodd (nondegenerate_polarBilin_quadOdd n _ h2) (by omega)
    (by omega) (centerScalar_quadOdd h2 hn3) _ ?_ ?_ (fundCorr_odd hp2 hq hadm).1
  · intro R hR
    exact e189_commutator_eq_of_le (hperf R hR)
  · intro R hR g
    exact conjSub_mem_fundamentalSubgroups hR g

theorem e189ModelAt_plus_of_five_le (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n) :
    E189ModelAt p e .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ → Gaps.FundPerfect .POmegaPlus M.D →
      E189AtFam M.K (fundamentalSubgroups .POmegaPlus M.D) := by
    intro M hM hP
    subst hM
    refine e189AtFam_spin_of_ne8 hodd (nondegenerate_polarBilin_quadPlus n _) (by omega)
      (by omega) (centerScalar_quadPlus hn3) _ ?_ ?_ (fundCorr_plus hp2 hq hn4).1
    · intro R hR
      exact e189_commutator_eq_of_le (hP R hR)
    · intro R hR g
      exact conjSub_mem_fundamentalSubgroups hR g
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) hperf

theorem e189ModelAt_minus_of_five_le (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hn5 : 5 ≤ n) :
    E189ModelAt p e .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  show E189AtFam (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr p e)))
  refine e189AtFam_spin_of_ne8 hodd
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e)) (by omega)
    (by omega) (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) _ ?_ ?_
    (fundCorr_minus hp2 hq hadm).1
  · intro R hR
    exact e189_commutator_eq_of_le (hperf R hR)
  · intro R hR g
    exact conjSub_mem_fundamentalSubgroups hR g

theorem e189ModelAt_minus_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .POmegaMinus 4 p e) : E189ModelAt p e .POmegaMinus 4 := by
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 := ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField p e) = 2 * (4 - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus 4 p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  show E189AtFam
    (spinGroup (quadMinus 4 (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (fundamentalSubgroups .POmegaMinus (Twisted.minusDatum 4 (minusCoeffs_irr p e)))
  refine e189AtFam_spin_of_noOrth hodd
    (nondegenerate_polarBilin_quadMinus_of_finite 4 _ (minusCoeffs_irr p e)) (by omega)
    (centerScalar_quadMinus le_rfl (minusCoeffs_irr p e))
    (fun F₀ F₁ hF => false_of_orth_quadMinus_four h2 (minusCoeffs_irr p e) h4 F₀ F₁ hF) _ ?_ ?_
    (fundCorr_minus hp2 hq hadm).1
  · intro R hR
    exact e189_commutator_eq_of_le (hperf R hR)
  · intro R hR g
    exact conjSub_mem_fundamentalSubgroups hR g

theorem e189ModelAt_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) : E189ModelAt p e .POmegaMinus n := by
  by_cases hn : n = 4
  · subst hn
    exact e189ModelAt_minus_four hp2 hq hadm
  · exact e189ModelAt_minus_of_five_le hp2 hq hadm (by have := hadm.2.2; omega)

end CFSG.ClassicalInvolution.Asc77
