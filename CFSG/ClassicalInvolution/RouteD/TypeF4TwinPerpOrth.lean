module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrth
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpArith
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

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Abstract

variable {X : Type} [Group X] {K V W : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
  {Q₂ : QuadraticForm K W}

theorem orth_layer_eq_f4 (hodd : Odd (Nat.card K)) (π : X →* (V ≃ₗ[K] V))
    (hker : π.ker ≤ Subgroup.center X) {Fund : Set (Subgroup X)}
    (hperf : ∀ R ∈ Fund, ⁅R, R⁆ = R) (hmap : ∀ R ∈ Fund, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ Fund, R.map π = L) {R₀ : Subgroup X} (hR₀ : R₀ ∈ Fund)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂)))
    (hN : Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} = f4Core (Nat.card K) + 1) :
    f4Core (Nat.card K) * o4Val (Nat.card K) = 2 * Nat.card (OFrame Q₂) := by
  have h := orth_layer_count hodd π hker hperf hmap hsurj hR₀ e hN
  rw [card_o4_val] at h
  have h' : (f4Core (Nat.card K) + 1) * o4Val (Nat.card K) =
      f4Core (Nat.card K) * o4Val (Nat.card K) + o4Val (Nat.card K) := by ring
  omega

end Abstract

section Models

variable {p f : ℕ} [Fact p.Prime]

theorem f4_eq_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {R₀ : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D ∧
        Commutes S R₀} = f4Core (p ^ f) + 1) : n = 4 := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have h2 := ModelFacts.two_ne_zero_galoisField f hp2
  have hf : 1 ≤ f := hadm.2.1
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hcorr := fundCorr_odd hp2 hq hadm
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := orth_layer_eq_f4 (Q := quadOdd (j + 3) (GaloisField p f)) hodd
    (spinAction (quadOdd (j + 3) (GaloisField p f))) (ker_spinAction_le_center _)
    (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
    ((oddIsometry (GaloisField p f) (j + 2)).trans
      (hypSumCongr (oddIsometry (GaloisField p f) (j + 1)))) (by rw [hcard]; exact hN)
  rcases j with _ | j
  · exfalso
    have e0 : Nat.card (OFrame (quadOdd (0 + 1) (GaloisField p f))) = 0 :=
      card_frame_odd_one (GaloisField p f) h2
    rw [e0, hcard] at key
    exact f4Core_mul_o4Val_ne_zero hq (by simpa using key)
  · rw [card_frame_odd (GaloisField p f) h2 j, hcard] at key
    have := f4_odd_eq Fact.out hp2 hf rfl hq key
    omega

theorem f4_false_plus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n p f)
    {R₀ : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n p f Fact.out).D ∧
        Commutes S R₀} = f4Core (p ^ f) + 1) : False := by
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
        Commutes S R₀} = f4Core (p ^ f) + 1 → False := by
    intro M hM R₀ hR₀ hperf hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := orth_layer_eq_f4 (Q := quadPlus (j + 4) (GaloisField p f)) hodd
      (spinAction (quadPlus (j + 4) (GaloisField p f))) (ker_spinAction_le_center _)
      (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2 hR₀
      ((plusIsometry (GaloisField p f) (j + 3)).trans
        (hypSumCongr (plusIsometry (GaloisField p f) (j + 2)))) (by rw [hcard]; exact hN)
    rw [card_frame_plus (GaloisField p f) j, hcard] at hk
    exact f4_plus_impossible Fact.out hp2 hf rfl hq hk
  exact key _ (ModelFacts.modelUniv_POmegaPlus hn3) R₀ hR₀ hperf hN

theorem f4_false_minus (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaMinus n p f)
    {R₀ : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n p f Fact.out).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n p f Fact.out).D ∧
        Commutes S R₀} = f4Core (p ^ f) + 1) : False := by
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
  have key := orth_layer_eq_f4
    (Q := quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2) hodd
    (spinAction (quadMinus (j + 4) (GaloisField p f) (minusCoeffs p f).1 (minusCoeffs p f).2))
    (ker_spinAction_le_center _) (fun R hR => eq_commutator_of_le (hperf R hR)) hcorr.1 hcorr.2
    hR₀ ((minusIsometry (GaloisField p f) (j + 2) (minusCoeffs p f).1 (minusCoeffs p f).2).trans
      (hypSumCongr (minusIsometry (GaloisField p f) (j + 1) (minusCoeffs p f).1
        (minusCoeffs p f).2))) (by rw [hcard]; exact hN)
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadMinus (0 + 2) (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = 0 := card_frame_minus_two (GaloisField p f) hirr
    rw [e0, hcard] at key
    exact f4Core_mul_o4Val_ne_zero hq (by simpa using key)
  · have e1 : Nat.card (OFrame (quadMinus (j + 1 + 2) (GaloisField p f) (minusCoeffs p f).1
        (minusCoeffs p f).2)) = ((Nat.card (GaloisField p f) ^ (j + 1 + 1 + 1) + 1) *
          (Nat.card (GaloisField p f) ^ (j + 1 + 1) - 1)) *
          Nat.card (GaloisField p f) ^ (2 * (j + 1 + 1)) *
        (((Nat.card (GaloisField p f) ^ (j + 1 + 1) + 1) *
          (Nat.card (GaloisField p f) ^ (j + 1) - 1)) *
          Nat.card (GaloisField p f) ^ (2 * (j + 1))) :=
      card_frame_minus (GaloisField p f) h2 hirr j
    rw [e1, hcard] at key
    exact f4_minus_impossible Fact.out hp2 hf rfl hq key

end Models

end CFSG.ClassicalInvolution.RouteD.NonClassical
