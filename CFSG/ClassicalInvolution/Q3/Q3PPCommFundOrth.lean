module

public import CFSG.ClassicalInvolution.Q3.Q3T7E9OrthModel
public import CFSG.ClassicalInvolution.Q3.LieSystem

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts (Gen3)
open CFSG.ClassicalInvolution.Q3.Q3T7E9

section Generic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem commFund_spin_of_corr [Nontrivial V] (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (𝓕 : Set (Subgroup (spinGroup Q)))
    (hgen : ∀ R ∈ 𝓕, Gen3 R) (hcorr : ∀ R ∈ 𝓕, R.map (spinAction Q) ∈ fundSet Q)
    (hlift : ∀ L ∈ fundSet Q, ∃ R ∈ 𝓕, R.map (spinAction Q) = L) :
    ∀ R ∈ 𝓕, ∃ S ∈ 𝓕, Commutes R S := by
  intro R hR
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  set π := spinAction Q with hπ
  have hker : π.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hk2 : ∀ x ∈ π.ker, x * x = 1 := spinAction_ker_sq h2 hQ
  have hk3 : ∀ x ∈ π.ker, x ^ 3 = 1 → x = 1 := fun x hx h3 =>
    CFSG.ClassicalInvolution.ModelFacts.eq_one_of_sq_eq_one_of_pow_three (hk2 x hx) h3
  obtain ⟨i, hi⟩ := hcorr R hR
  obtain ⟨L', hL', -, hcomm, -⟩ := IsFundamental.exists_twin hodd hi
  obtain ⟨S, hS, hSL⟩ := hlift L' ⟨i, hL'⟩
  refine ⟨S, hS, fun a ha b hb => ?_⟩
  refine CFSG.ClassicalInvolution.ModelFacts.commute_of_map_commute_of_gen3 π hker hk3
    (hgen R hR) (b := b) (fun a' ha' => ?_) a ha
  have hb' : π b ∈ L' := hSL ▸ Subgroup.mem_map_of_mem π hb
  exact hcomm (π a') (Subgroup.mem_map_of_mem π ha') (π b) hb'

end Generic


section Models

theorem commFund_pomegaOdd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1) :
    ∀ R ∈ (CompData.model .POmegaOdd n).fund,
      ∃ S ∈ (CompData.model .POmegaOdd n).fund, Commutes R S := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  have : Nontrivial (Fin n ⊕ Fin n ⊕ Unit → GaloisField 3 1) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField 3 1) (by omega)
  show ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField 3 1)),
    ∃ S ∈ fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField 3 1)), Commutes R S
  have hcorr := fundCorr_odd_of_odd (by norm_num) le_rfl hadm
  exact commFund_spin_of_corr hodd (nondegenerate_polarBilin_quadOdd n _ h2) _ hgen hcorr.1
    hcorr.2

theorem commFund_pomegaMinus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1) :
    ∀ R ∈ (CompData.model .POmegaMinus n).fund,
      ∃ S ∈ (CompData.model .POmegaMinus n).fund, Commutes R S := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  have : Nontrivial (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 3 1) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField 3 1) (by omega)
  show ∀ R ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr 3 1)),
    ∃ S ∈ fundamentalSubgroups .POmegaMinus (Twisted.minusDatum n (minusCoeffs_irr 3 1)),
      Commutes R S
  have hcorr := fundCorr_minus_of_odd (by norm_num) le_rfl hadm
  exact commFund_spin_of_corr hodd
    (nondegenerate_polarBilin_quadMinus_of_finite n _ (minusCoeffs_irr 3 1)) _ hgen hcorr.1
    hcorr.2

theorem commFund_pomegaPlus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1) :
    ∀ R ∈ (CompData.model .POmegaPlus n).fund,
      ∃ S ∈ (CompData.model .POmegaPlus n).fund, Commutes R S := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hodd := odd_card_galoisField_of_ne_two (p := 3) (e := 1) (by norm_num) le_rfl
  have hdim : Module.finrank (GaloisField 3 1) (Fin n ⊕ Fin n → GaloisField 3 1) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hgen : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Fact.out).D,
      Gen3 R := fun R hR =>
    gen3_of_mem_fundamentalSubgroups_three (by simp [IsFundTag]) hadm (by decide) (by decide) hR
  have : Nontrivial (Fin n ⊕ Fin n → GaloisField 3 1) :=
    Module.nontrivial_of_finrank_pos (R := GaloisField 3 1) (by omega)
  have hcorr := fundCorr_plus_of_odd (by norm_num) le_rfl hadm hn4
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField 3 1)),
      plusDatum n (GaloisField 3 1) hn3⟩ → (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, Gen3 R) →
      ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D,
        ∃ S ∈ fundamentalSubgroups .POmegaPlus M.D, Commutes R S := by
    intro M hM hG
    subst hM
    exact commFund_spin_of_corr hodd (nondegenerate_polarBilin_quadPlus n _) _ hG hcorr.1 hcorr.2
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3) hgen

end Models

end CFSG.ClassicalInvolution.Q3.Q3PP
