module

public import CFSG.ClassicalInvolution.RouteD.TWYLayer
public import CFSG.ClassicalInvolution.Q3.Q3TY13
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.TWY
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame


section Count

variable {X Y : Type} [Group X] [Group Y]

theorem card_commuting_map3 {π : X →* Y} {Fund : Set (Subgroup X)} {Fund' : Set (Subgroup Y)}
    {Z' : Subgroup Y} (cq : Q3W.CentralQuot3 π Fund Fund' Z') (R₀ : Subgroup X) :
    Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} =
      Nat.card {S' : Subgroup Y // S' ∈ Fund' ∧ Commutes S' (R₀.map π)} := by
  refine Nat.card_eq_of_bijective
    (fun S => ⟨S.1.map π, cq.map_mem _ S.2.1, (cq.commutes_iff S.2.1).mpr S.2.2⟩) ⟨?_, ?_⟩
  · intro S₁ S₂ h
    exact Subtype.ext (cq.map_inj S₁.2.1 S₂.2.1 (congrArg Subtype.val h))
  · rintro ⟨S', hS', hc⟩
    obtain ⟨S, hS, rfl⟩ := cq.surj S' hS'
    exact ⟨⟨S, hS, (cq.commutes_iff hS).mp hc⟩, rfl⟩

variable {K V W : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] {Q : QuadraticForm K V} {Q₂ : QuadraticForm K W}

theorem orth_layer_count3 (hodd : Odd (Nat.card K)) {π : X →* (V ≃ₗ[K] V)}
    {Fund : Set (Subgroup X)} {Z' : Subgroup (V ≃ₗ[K] V)}
    (cq : Q3W.CentralQuot3 π Fund (fundSet Q) Z') {R₀ : Subgroup X} (hR₀ : R₀ ∈ Fund)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) {N : ℕ}
    (hN : Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} = N) :
    2 * Nat.card (OFrame Q₂) +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  have : Finite V := Module.finite_of_finite K
  obtain ⟨i, F₀, hF₀, -⟩ := cq.map_mem R₀ hR₀
  have hcard := card_commuting_map3 cq R₀
  rw [hN, hF₀] at hcard
  obtain ⟨F₁, ι, hι, hinj, hrange⟩ := exists_frame_perp_emb e
  have h1 := two_mul_card_frames_perp hodd F₀
  rw [card_frames_perp_conj hodd F₀ F₁, card_frames_perp F₁ ι hι hinj hrange, ← hcard] at h1
  exact h1

end Count

section Models

theorem layerCount3_odd {n : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D)
    {N : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = N) :
    ∃ j, n = j + 3 ∧ 2 * cOdd 3 j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) := by
  have hn3 : 3 ≤ n := hadm.2.2.1
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
  have key := orth_layer_count3 (Q := quadOdd (j + 3) (GaloisField 3 1)) Q3W.odd_gf3
    (Q3TWY.centralQuot3_odd hn3) hR₀ ((oddIsometry (GaloisField 3 1) (j + 2)).trans
      (hypSumCongr (oddIsometry (GaloisField 3 1) (j + 1)))) hN
  refine ⟨j, rfl, ?_⟩
  rcases j with _ | j
  · rw [card_frame_odd_one (GaloisField 3 1) h2] at key
    exact key
  · rw [card_frame_odd (GaloisField 3 1) h2 j, Q3W.card_gf3] at key
    exact key

theorem layerCount3_minus {n : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D)
    {N : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaMinus (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = N) :
    ∃ j, n = j + 4 ∧ 2 * cMinus 3 j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hirr := minusCoeffs_irr 3 1
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
  have key := orth_layer_count3
    (Q := quadMinus (j + 4) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
    Q3W.odd_gf3 (Q3TY.centralQuot3_minus hadm) hR₀
    ((minusIsometry (GaloisField 3 1) (j + 2) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).trans
      (hypSumCongr (minusIsometry (GaloisField 3 1) (j + 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2))) hN
  refine ⟨j, rfl, ?_⟩
  rcases j with _ | j
  · rw [card_frame_minus_two (GaloisField 3 1) hirr] at key
    exact key
  · rw [card_frame_minus (GaloisField 3 1) h2 hirr j, Q3W.card_gf3] at key
    exact key

theorem layerCount3_plus {n : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n 3 1)
    {R₀ : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D)
    {N : ℕ} (hN : Nat.card {S : Subgroup (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K //
      S ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D ∧
        Commutes S R₀} = N) :
    ∃ j, n = j + 4 ∧ 2 * framesPlus 3 j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) := by
  have hn4 : 4 ≤ n := hadm.2.2
  have hn3 : 3 ≤ n := by omega
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus n (GaloisField 3 1)),
      plusDatum n (GaloisField 3 1) hn3⟩ → ∀ R₀ : Subgroup M.K,
      R₀ ∈ fundamentalSubgroups .POmegaPlus M.D →
      Nat.card {S : Subgroup M.K // S ∈ fundamentalSubgroups .POmegaPlus M.D ∧
        Commutes S R₀} = N → ∃ j, n = j + 4 ∧ 2 * framesPlus 3 j +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) := by
    intro M hM R₀ hR₀ hN
    subst hM
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
    have hk := orth_layer_count3 (Q := quadPlus (j + 4) (GaloisField 3 1)) Q3W.odd_gf3
      (Q3TY.centralQuot3_plus hn4) hR₀
      ((plusIsometry (GaloisField 3 1) (j + 3)).trans
        (hypSumCongr (plusIsometry (GaloisField 3 1) (j + 2)))) hN
    refine ⟨j, rfl, ?_⟩
    rw [card_frame_plus (GaloisField 3 1) j, Q3W.card_gf3] at hk
    exact hk
  exact key _ (RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3) R₀ hR₀ hN

end Models

end CFSG.ClassicalInvolution.Q3.Q3TIY
