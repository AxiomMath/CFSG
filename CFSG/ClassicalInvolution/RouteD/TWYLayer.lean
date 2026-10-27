module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth
public import CFSG.ClassicalInvolution.RouteD.TWYArith

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TwinY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

@[expose] def cOdd (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => framesOdd q j

@[expose] def cMinus (q : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => framesMinus q j

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem layerCount_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaOdd) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {N : ℕ}
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = N) :
    ∃ j, n = j + 3 ∧ 2 * cOdd (p ^ f) j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) := by
  subst ht he
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  have hf : 1 ≤ e := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_odd hp2 hq hadm
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := orth_layer_count (Q := quadOdd (j + 3) (GaloisField p e)) hodd
    (spinAction (quadOdd (j + 3) (GaloisField p e))) (ker_spinAction_le_center _)
    (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
    ((oddIsometry (GaloisField p e) (j + 2)).trans
      (hypSumCongr (oddIsometry (GaloisField p e) (j + 1)))) hN
  refine ⟨j, rfl, ?_⟩
  rcases j with _ | j
  · rw [card_frame_odd_one (GaloisField p e) h2] at key
    exact key
  · rw [card_frame_odd (GaloisField p e) h2 j, hcard] at key
    exact key

theorem layerCount_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {N : ℕ}
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = N) :
    ∃ j, n = j + 4 ∧ 2 * framesPlus (p ^ f) j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) := by
  subst ht he
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hf : 1 ≤ e := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_plus hp2 hq hn4
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p e)),
      plusDatum n (GaloisField p e) hn3⟩ → ∀ R₀ : Subgroup M.K,
      R₀ ∈ fundamentalSubgroups .POmegaPlus M.D → Gaps.FundPerfect .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = N → ∃ j, n = j + 4 ∧ 2 * framesPlus (p ^ e) j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p e))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p e))) := by
    intro M hM R₀ hR₀ hperf hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := orth_layer_count (Q := quadPlus (j + 4) (GaloisField p e)) hodd
      (spinAction (quadPlus (j + 4) (GaloisField p e))) (ker_spinAction_le_center _)
      (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
      ((plusIsometry (GaloisField p e) (j + 3)).trans
        (hypSumCongr (plusIsometry (GaloisField p e) (j + 2)))) hN
    refine ⟨j, rfl, ?_⟩
    rw [card_frame_plus (GaloisField p e) j, hcard] at hk
    exact hk
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) R₀ hR₀ hperf hN

theorem layerCount_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaMinus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {N : ℕ}
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = N) :
    ∃ j, n = j + 4 ∧ 2 * cMinus (p ^ f) j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) := by
  subst ht he
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField e hp2
  have hf : 1 ≤ e := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus n p e Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_minus hp2 hq hadm
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (by omega)
  have hirr := minusCoeffs_irr p e
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := orth_layer_count
    (Q := quadMinus (j + 4) (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2) hodd
    (spinAction (quadMinus (j + 4) (GaloisField p e) (minusCoeffs p e).1 (minusCoeffs p e).2))
    (ker_spinAction_le_center _) (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2
    hR₀ ((minusIsometry (GaloisField p e) (j + 2) (minusCoeffs p e).1 (minusCoeffs p e).2).trans
      (hypSumCongr (minusIsometry (GaloisField p e) (j + 1) (minusCoeffs p e).1
        (minusCoeffs p e).2))) hN
  refine ⟨j, rfl, ?_⟩
  rcases j with _ | j
  · rw [card_frame_minus_two (GaloisField p e) hirr] at key
    exact key
  · rw [card_frame_minus (GaloisField p e) h2 hirr j, hcard] at key
    exact key

end Models

end CFSG.ClassicalInvolution.RouteD.TWY
