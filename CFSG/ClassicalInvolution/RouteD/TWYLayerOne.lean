module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

theorem pow_sub_one_ne_zero {q k : ℕ} (hq : 2 ≤ q) (hk : k ≠ 0) : q ^ k - 1 ≠ 0 := by
  have : 1 < q ^ k := Nat.one_lt_pow hk (by omega)
  omega

theorem eq_zero_of_two_mul_add_eq {X O : ℕ} (h : 2 * X + O = 1 * O) : X = 0 := by omega

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem layerOne_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {R₀ : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D ∧
        Commutes S R₀} = 1) : n = 3 := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField f hp2
  have hf : 1 ≤ f := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_odd hp2 hq hadm
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := orth_layer_count (Q := quadOdd (j + 3) (GaloisField p f)) hodd
    (spinAction (quadOdd (j + 3) (GaloisField p f))) (ker_spinAction_le_center _)
    (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
    ((oddIsometry (GaloisField p f) (j + 2)).trans
      (hypSumCongr (oddIsometry (GaloisField p f) (j + 1)))) hN
  rcases j with _ | j
  · rfl
  · exfalso
    have h0 := eq_zero_of_two_mul_add_eq key
    rw [card_frame_odd (GaloisField p f) h2 j, hcard] at h0
    have h5 : 2 ≤ p ^ f := by omega
    have hpos : 0 < p ^ f := by omega
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (pow_sub_one_ne_zero h5 (by omega)) (pow_pos hpos _).ne')
      (Nat.mul_ne_zero (pow_sub_one_ne_zero h5 (by omega)) (pow_pos hpos _).ne') h0

theorem layerOne_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f)
    {R₀ : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D ∧
        Commutes S R₀} = 1) : False := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hf : 1 ≤ f := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_plus hp2 hq hn4
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p f)),
      plusDatum n (GaloisField p f) hn3⟩ → ∀ R₀ : Subgroup M.K,
      R₀ ∈ fundamentalSubgroups .POmegaPlus M.D → Gaps.FundPerfect .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = 1 → False := by
    intro M hM R₀ hR₀ hperf hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := orth_layer_count (Q := quadPlus (j + 4) (GaloisField p f)) hodd
      (spinAction (quadPlus (j + 4) (GaloisField p f))) (ker_spinAction_le_center _)
      (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
      ((plusIsometry (GaloisField p f) (j + 3)).trans
        (hypSumCongr (plusIsometry (GaloisField p f) (j + 2)))) hN
    have h0 := eq_zero_of_two_mul_add_eq hk
    rw [card_frame_plus (GaloisField p f) j, hcard] at h0
    have h5 : 2 ≤ p ^ f := by omega
    have hpos : 0 < p ^ f := by omega
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_sub_one_ne_zero h5 (by omega))
      (Nat.succ_ne_zero _)) (pow_pos hpos _).ne')
      (Nat.mul_ne_zero (Nat.mul_ne_zero (pow_sub_one_ne_zero h5 (by omega)) (Nat.succ_ne_zero _))
        (pow_pos hpos _).ne') h0
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) R₀ hR₀ hperf hN

theorem layerOne_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f)
    {R₀ : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D ∧
        Commutes S R₀} = 1) : n = 4 := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField f hp2
  have hf : 1 ≤ f := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_minus hp2 hq hadm
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hirr := minusCoeffs_irr p f
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := orth_layer_count
    (Q := quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) hodd
    (spinAction (quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (ker_spinAction_le_center _) (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2
    hR₀ ((minusIsometry (GaloisField p f) (j + 2) (minusCoeffs p f).1 (minusCoeffs p f).2).trans
      (hypSumCongr (minusIsometry (GaloisField p f) (j + 1) (minusCoeffs p f).1
        (minusCoeffs p f).2))) hN
  rcases j with _ | j
  · rfl
  · exfalso
    have h0 := eq_zero_of_two_mul_add_eq key
    rw [card_frame_minus (GaloisField p f) h2 hirr j, hcard] at h0
    have h5 : 2 ≤ p ^ f := by omega
    have hpos : 0 < p ^ f := by omega
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero _)
      (pow_sub_one_ne_zero h5 (by omega))) (pow_pos hpos _).ne')
      (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero _) (pow_sub_one_ne_zero h5 (by omega)))
        (pow_pos hpos _).ne') h0

end Models


section General

variable {p f : ℕ} [Fact p.Prime]

theorem layerOne_odd' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaOdd) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 1) :
    n = 3 := by
  subst ht he
  exact layerOne_odd hp2 hq hadm hR₀ hN

theorem layerOne_plus' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaPlus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 1) :
    False := by
  subst ht he
  exact layerOne_plus hp2 hq hadm hR₀ hN

theorem layerOne_minus' (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag} {n e : ℕ}
    (ht : t = .POmegaMinus) (he : e = f) (hadm : StatedLieAdmissible t n p e)
    {R₀ : Subgroup (modelUniv t n p e Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv t n p e Fact.out).K //
      S ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D ∧ Commutes S R₀} = 1) :
    n = 4 := by
  subst ht he
  exact layerOne_minus hp2 hq hadm hR₀ hN

end General

end CFSG.ClassicalInvolution.RouteD.TWY
