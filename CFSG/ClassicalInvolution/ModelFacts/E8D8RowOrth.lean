module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowArith
public import CFSG.ClassicalInvolution.ModelFacts.E8D8RowFund
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

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Abstract

variable {X : Type} [Group X] {K V W : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
  {Q₂ : QuadraticForm K W}

theorem card_frame_eq_of_layer (hodd : Odd (Nat.card K)) (π : X →* (V ≃ₗ[K] V))
    (hker : π.ker ≤ Subgroup.center X) {Fund : Set (Subgroup X)}
    (hperf : ∀ R ∈ Fund, ⁅R, R⁆ = R) (hmap : ∀ R ∈ Fund, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ Fund, R.map π = L) {R₀ : Subgroup X} (hR₀ : R₀ ∈ Fund)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) {m F₁₂ : ℕ}
    (hN : Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) = 2 * F₁₂) :
    Nat.card (OFrame Q₂) = F₁₂ := by
  have h := orth_layer_count hodd π hker hperf hmap hsurj hR₀ e hN
  have h' : (m + 1) * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by ring
  omega

end Abstract

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem card_frame_plus_eq (F : Type) [Field F] [Finite F] (j : ℕ) :
    Nat.card (OFrame (quadPlus (j + 1 + 1) F)) = framePlus (Nat.card F) j :=
  card_frame_plus F j

theorem card_frame_plus_six (F : Type) [Field F] [Finite F] :
    Nat.card (OFrame (quadPlus 6 F)) = framePlus (Nat.card F) 4 :=
  card_frame_plus F 4

theorem d8_false_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {R₀ : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField p f)))) : False := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, h4⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField f hp2
  have hf : 1 ≤ f := hadm.2.1
  have hperf : RouteD.Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_odd hp2 hq hadm
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hq5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := card_frame_eq_of_layer (Q := quadOdd (j + 3) (GaloisField p f)) hodd
    (spinAction (quadOdd (j + 3) (GaloisField p f))) (ker_spinAction_le_center _)
    (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
    ((oddIsometry (GaloisField p f) (j + 2)).trans
      (hypSumCongr (oddIsometry (GaloisField p f) (j + 1)))) hN hm
  rw [card_frame_plus_six] at key
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadOdd (0 + 1) (GaloisField p f))) = 0 :=
      card_frame_odd_one (GaloisField p f) h2
    rw [e0] at key
    exact (framePlus_pos (by omega) 4).ne key
  · have e1 : Nat.card (OFrame (quadOdd (j + 1 + 1) (GaloisField p f))) =
        frameOdd (Nat.card (GaloisField p f)) j := card_frame_odd (GaloisField p f) h2 j
    rw [e1] at key
    exact frameOdd_ne_framePlus_four Fact.out hp2 hf hcard hq5 key

theorem d8_eq_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f)
    {R₀ : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField p f)))) : n = 8 := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hf : 1 ≤ f := hadm.2.1
  have hperf : RouteD.Gaps.FundPerfect .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_plus hp2 hq hn4
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hq5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField p f)),
      plusDatum n (GaloisField p f) hn3⟩ → ∀ R₀ : Subgroup M.K,
      R₀ ∈ fundamentalSubgroups .POmegaPlus M.D → RouteD.Gaps.FundPerfect .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = m + 1 → n = 8 := by
    intro M hM R₀ hR₀ hperf hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := card_frame_eq_of_layer (Q := quadPlus (j + 4) (GaloisField p f)) hodd
      (spinAction (quadPlus (j + 4) (GaloisField p f))) (ker_spinAction_le_center _)
      (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
      ((plusIsometry (GaloisField p f) (j + 3)).trans
        (hypSumCongr (plusIsometry (GaloisField p f) (j + 2)))) hN hm
    rw [card_frame_plus_eq, card_frame_plus_six] at hk
    have := framePlus_eq_framePlus_four Fact.out hp2 hf hcard hq5 hk
    omega
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) R₀ hR₀ hperf hN

theorem d8_false_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f)
    {R₀ : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D)
    {m : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D ∧
        Commutes S R₀} = m + 1)
    (hm : m * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) =
      2 * Nat.card (OFrame (quadPlus 6 (GaloisField p f)))) : False := by
  have hn4 : 4 ≤ n := hadm.2.2
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField f hp2
  have hf : 1 ≤ f := hadm.2.1
  have hperf : RouteD.Gaps.FundPerfect .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D :=
    RouteD.Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_minus hp2 hq hadm
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hq5 : 5 ≤ Nat.card (GaloisField p f) := by rw [hcard]; exact hq
  have hirr := minusCoeffs_irr p f
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := card_frame_eq_of_layer
    (Q := quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) hodd
    (spinAction (quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (ker_spinAction_le_center _) (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2
    hR₀ ((minusIsometry (GaloisField p f) (j + 2) (minusCoeffs p f).1 (minusCoeffs p f).2).trans
      (hypSumCongr (minusIsometry (GaloisField p f) (j + 1) (minusCoeffs p f).1
        (minusCoeffs p f).2))) hN hm
  rw [card_frame_plus_six] at key
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadMinus (0 + 2) (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = 0 := card_frame_minus_two (GaloisField p f) hirr
    rw [e0] at key
    exact (framePlus_pos (by omega) 4).ne key
  · have e1 : Nat.card (OFrame (quadMinus (j + 1 + 2) (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = frameMinus (Nat.card (GaloisField p f)) j :=
      card_frame_minus (GaloisField p f) h2 hirr j
    rw [e1] at key
    exact frameMinus_ne_framePlus_four Fact.out hp2 hf hcard hq5 key

end Models

end CFSG.ClassicalInvolution.ModelFacts.E8D8
