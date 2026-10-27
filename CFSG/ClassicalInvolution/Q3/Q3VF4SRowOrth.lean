module

public import CFSG.ClassicalInvolution.Q3.Q3E8BRowOrth
public import CFSG.ClassicalInvolution.Q3.Q3VF4SRowArith
public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpOrth

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.RouteD.NonClassical
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.ModelFacts.TG3 (natCard_galoisField_three
  odd_natCard_galoisField_three two_ne_zero_three)
open CFSG.ClassicalInvolution.RouteD (modelUniv_POmegaPlus_eq)
open CFSG.ClassicalInvolution.Q3.Q3W (orth_layer_count3)
open CFSG.ClassicalInvolution.Q3.Q3W.EB (central3_odd central3_plus central3_minus
  finite_spin_odd finite_spin_plus finite_spin_minus)
open CFSG.ClassicalInvolution.Q3.Q3W.EX (Central3)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

set_option linter.unusedSectionVars false


section Abstract

variable {X : Type} [Group X] [Finite X] {K V W : Type} [Field K] [Finite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
  {Q₂ : QuadraticForm K W}

theorem orth_layer_eq_f43 (hodd : Odd (Nat.card K)) {π : X →* (V ≃ₗ[K] V)}
    {𝓕 : Set (Subgroup X)} (h : Central3 π 𝓕 (fundSet Q)) {R₀ : Subgroup X} (hR₀ : R₀ ∈ 𝓕)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂)))
    (hN : Nat.card {S : Subgroup X // S ∈ 𝓕 ∧ Commutes S R₀} = f4Core (Nat.card K) + 1) :
    f4Core (Nat.card K) * o4Val (Nat.card K) = 2 * Nat.card (OFrame Q₂) := by
  have h1 := orth_layer_count3 hodd h hR₀ e hN
  rw [card_o4_val] at h1
  have h' : (f4Core (Nat.card K) + 1) * o4Val (Nat.card K) =
      f4Core (Nat.card K) * o4Val (Nat.card K) + o4Val (Nat.card K) := by ring
  omega

end Abstract

theorem f4_eq_odd3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = f4Core 3 + 1) : n = 4 := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hodd := odd_natCard_galoisField_three
  have h2 := two_ne_zero_three
  have : Finite (spinGroup (quadOdd n 𝔽₃)) := finite_spin_odd hadm
  have hC := central3_odd hadm
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := orth_layer_eq_f43 (Q := quadOdd (j + 3) 𝔽₃) hodd hC hR₀
    ((oddIsometry 𝔽₃ (j + 2)).trans (hypSumCongr (oddIsometry 𝔽₃ (j + 1))))
    (by rw [natCard_galoisField_three]; exact hN)
  rcases j with _ | j
  · exfalso
    have e0 : Nat.card (OFrame (quadOdd (0 + 1) 𝔽₃)) = 0 := card_frame_odd_one 𝔽₃ h2
    rw [e0, natCard_galoisField_three] at key
    exact f4Core_mul_o4Val_ne_zero3 le_rfl (by simpa using key)
  · rw [card_frame_odd 𝔽₃ h2 j, natCard_galoisField_three] at key
    have := f4_odd_eq3 Nat.prime_three (by norm_num) le_rfl (by norm_num) le_rfl key
    omega

theorem f4_false_plus3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = f4Core 3 + 1) : False := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have hodd := odd_natCard_galoisField_three
  have : Finite (spinGroup (quadPlus n 𝔽₃)) := finite_spin_plus hadm hn3
  have hC := central3_plus hadm hn3
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n 𝔽₃), plusDatum n 𝔽₃ hn3⟩ →
      ∀ R₀ : Subgroup M.K, R₀ ∈ fundamentalSubgroups .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = f4Core 3 + 1 → False := by
    intro M hM R₀ hR₀ hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := orth_layer_eq_f43 (Q := quadPlus (j + 4) 𝔽₃) hodd hC hR₀
      ((plusIsometry 𝔽₃ (j + 3)).trans (hypSumCongr (plusIsometry 𝔽₃ (j + 2))))
      (by rw [natCard_galoisField_three]; exact hN)
    rw [card_frame_plus 𝔽₃ j, natCard_galoisField_three] at hk
    exact f4_plus_impossible3 Nat.prime_three (by norm_num) le_rfl (by norm_num) le_rfl hk
  exact key _ (modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) R₀ hR₀ hN

theorem f4_false_minus3 {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D)
    (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = f4Core 3 + 1) : False := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hodd := odd_natCard_galoisField_three
  have h2 := two_ne_zero_three
  have hirr := minusCoeffs_irr 3 1
  have : Finite (spinGroup (quadMinus n 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) :=
    finite_spin_minus hadm
  have hC := central3_minus hadm
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := orth_layer_eq_f43
    (Q := quadMinus (j + 4) 𝔽₃ (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) hodd hC hR₀
    ((minusIsometry 𝔽₃ (j + 2) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).trans
      (hypSumCongr (minusIsometry 𝔽₃ (j + 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (by rw [natCard_galoisField_three]; exact hN)
  rcases j with _ | j
  · have e0 : Nat.card (OFrame (quadMinus (0 + 2) 𝔽₃ (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)) = 0 := card_frame_minus_two 𝔽₃ hirr
    rw [e0, natCard_galoisField_three] at key
    exact f4Core_mul_o4Val_ne_zero3 le_rfl (by simpa using key)
  · rw [card_frame_minus 𝔽₃ h2 hirr j, natCard_galoisField_three] at key
    exact f4_minus_impossible3 Nat.prime_three (by norm_num) le_rfl (by norm_num) le_rfl key

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
