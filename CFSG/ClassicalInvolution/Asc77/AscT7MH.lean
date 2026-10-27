module

public import CFSG.ClassicalInvolution.Asc77.AscT7MG
import CFSG.ClassicalInvolution.Orders.OrthogonalNeg

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic

variable {p e : ℕ} [Fact p.Prime]


theorem twinSqAlpha_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p e) : TwinSqAlpha p e .POmegaOdd n := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p e) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have : Group.IsPerfect (spinGroup (quadOdd n (GaloisField p e))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaOdd) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaOdd) (n := n) trivial hadm
    (by simp)
  show TwinSqAlphaOn .POmegaOdd ⟨spinGroup (quadOdd n (GaloisField p e)),
    oddDatum n (GaloisField p e)⟩
  refine twinSqAlphaOn_of_spin_neg hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadOdd n _ h2) (range_spinAction_quadOdd h2 hn3)
    (centerScalar_quadOdd h2 hn3) (by omega) (neg_not_mem_elementaryGroup_quadOdd h2 hn3)
    (fun F₁ F₂ h => ?_) (fun H _ _ ψ hψ => liftSim_quadOdd hp2 hn3 he ψ hψ) _
    (fundCorr_odd hp2 hq hadm).1 hperf hnc
  have := finrank_eq_eight_of_proj hodd F₁ F₂ h
  omega

theorem twinSqAlpha_minus_of_nonsq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e)
    (hns : ¬ IsSquare ((-1 : GaloisField p e) ^ (n - 1) *
      (4 * (minusCoeffs p e).2 - (minusCoeffs p e).1 ^ 2))) :
    TwinSqAlpha p e .POmegaMinus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have : Group.IsPerfect (spinGroup (quadMinus n (GaloisField p e) (minusCoeffs p e).1
      (minusCoeffs p e).2)) := isPerfect_spinGroup_quadMinus hn4 (minusCoeffs_irr p e)
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaMinus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaMinus) (n := n) trivial
    hadm (by simp)
  show TwinSqAlphaOn .POmegaMinus ⟨spinGroup (quadMinus n (GaloisField p e)
    (minusCoeffs p e).1 (minusCoeffs p e).2), Twisted.minusDatum n (minusCoeffs_irr p e)⟩
  exact twinSqAlphaOn_of_spin_neg hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr p e))
    (range_spinAction_quadMinus hn4 (minusCoeffs_irr p e))
    (centerScalar_quadMinus hn4 (minusCoeffs_irr p e)) (by omega)
    (fun hmem => hns ((neg_mem_elementaryGroup_quadMinus_iff h2 (minusCoeffs_irr p e) hn4).mp hmem))
    (fun F₁ F₂ h => hproj_quadMinus hp2 hq hn4 F₁ F₂ h)
    (fun H _ _ ψ hψ => liftSim_quadMinus hp2 hn4 he ψ hψ) _ (fundCorr_minus hp2 hq hadm).1
    hperf hnc

theorem twinSqAlpha_plus_of_nonsq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n)
    (hns : ¬ IsSquare ((-1 : GaloisField p e) ^ n)) : TwinSqAlpha p e .POmegaPlus n := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hdim : Module.finrank (GaloisField p e) (Fin n ⊕ Fin n → GaloisField p e) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have : Group.IsPerfect (spinGroup (quadPlus n (GaloisField p e))) :=
    isPerfect_spinGroup_quadPlus hn3
  have hperf := Gaps.fundPerfect_modelUniv hp2 (t := .POmegaPlus) (n := n) (e := e) trivial hadm
    (by omega)
  have hnc := fund_noncentral_modelUniv (p := p) (e := e) (t := .POmegaPlus) (n := n) trivial hadm
    (by simp)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, R ≤ ⁅R, R⁆) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ r ∈ R, r ∈ Subgroup.center M.K → r = 1) →
        TwinSqAlphaOn .POmegaPlus M := by
    intro M hM hperf hnc
    subst hM
    refine twinSqAlphaOn_of_spin_neg hodd (five_le_card_galoisField hq)
      (nondegenerate_polarBilin_quadPlus n _) (range_spinAction_quadPlus hn3)
      (centerScalar_quadPlus hn3) (by omega)
      (fun hmem => hns ((neg_mem_elementaryGroup_quadPlus_iff h2 hn3).mp hmem))
      (fun F₁ F₂ h => ?_) (fun H _ _ ψ hψ => liftSim_quadPlus hp2 hn5 he ψ hψ) _
      (fundCorr_plus hp2 hq hn4).1 hperf hnc
    have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hperf hnc

theorem not_isSquare_minusCoeffs_disc (h2 : (2 : GaloisField p e) ≠ 0) :
    ¬ IsSquare ((minusCoeffs p e).1 ^ 2 - 4 * (minusCoeffs p e).2 : GaloisField p e) := by
  rintro ⟨d, hd⟩
  apply minusCoeffs_irr p e ((-(minusCoeffs p e).1 + d) / 2)
  field_simp
  linear_combination -hd

theorem twinSqAlpha_minus_of_even (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hn : Even n) :
    TwinSqAlpha p e .POmegaMinus n := by
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  refine twinSqAlpha_minus_of_nonsq hp2 hq hadm ?_
  have hodd : Odd (n - 1) := by
    have h4 : 4 ≤ n := hadm.2.2
    obtain ⟨m, hm⟩ := hn
    exact ⟨m - 1, by omega⟩
  rw [hodd.neg_one_pow]
  intro hsq
  apply not_isSquare_minusCoeffs_disc h2
  have : (-1 : GaloisField p e) * (4 * (minusCoeffs p e).2 - (minusCoeffs p e).1 ^ 2) =
      (minusCoeffs p e).1 ^ 2 - 4 * (minusCoeffs p e).2 := by ring
  rwa [this] at hsq

theorem twinSqAlpha_minus_of_sq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p e) (hm1 : IsSquare (-1 : GaloisField p e)) :
    TwinSqAlpha p e .POmegaMinus n := by
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  rcases Nat.even_or_odd n with hn | hn
  · exact twinSqAlpha_minus_of_even hp2 hq hadm hn
  refine twinSqAlpha_minus_of_nonsq hp2 hq hadm ?_
  have h4 : 4 ≤ n := hadm.2.2
  have hev : Even (n - 1) := by
    obtain ⟨m, hm⟩ := hn
    exact ⟨m, by omega⟩
  rw [hev.neg_one_pow, one_mul]
  intro hsq
  apply not_isSquare_minusCoeffs_disc h2
  have : (minusCoeffs p e).1 ^ 2 - 4 * (minusCoeffs p e).2 =
      (-1 : GaloisField p e) * (4 * (minusCoeffs p e).2 - (minusCoeffs p e).1 ^ 2) := by ring
  rw [this]
  exact hm1.mul hsq

theorem twinSqAlpha_plus_of_odd_nonsq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p e) (hn5 : 5 ≤ n) (hn : Odd n)
    (hm1 : ¬ IsSquare (-1 : GaloisField p e)) : TwinSqAlpha p e .POmegaPlus n := by
  refine twinSqAlpha_plus_of_nonsq hp2 hq hadm hn5 ?_
  rwa [hn.neg_one_pow]

end CFSG.ClassicalInvolution.Asc77
