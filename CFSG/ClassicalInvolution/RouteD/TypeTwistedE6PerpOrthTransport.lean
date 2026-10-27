module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthStd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped commutatorElement

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Bijection

variable {X Y : Type} [Group X] [Group Y]

theorem card_commuting_map (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {Fund : Set (Subgroup X)} {Fund' : Set (Subgroup Y)} (hperf : ∀ R ∈ Fund, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ Fund, R.map π ∈ Fund') (hsurj : ∀ L ∈ Fund', ∃ R ∈ Fund, R.map π = L)
    (R₀ : Subgroup X) :
    Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} =
      Nat.card {S' : Subgroup Y // S' ∈ Fund' ∧ Commutes S' (R₀.map π)} := by
  refine Nat.card_eq_of_bijective
    (fun S => ⟨S.1.map π, hmap _ S.2.1,
      (Gaps.commutes_map_iff hker (hperf _ S.2.1)).mpr S.2.2⟩) ⟨?_, ?_⟩
  · intro S₁ S₂ h
    exact Subtype.ext (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf _ S₁.2.1)
      (hperf _ S₂.2.1) (congrArg Subtype.val h))
  · rintro ⟨S', hS', hc⟩
    obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
    exact ⟨⟨S, hS, (Gaps.commutes_map_iff hker (hperf _ hS)).mp hc⟩, rfl⟩

end Bijection

section Count

variable {X : Type} [Group X] {K V W : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [AddCommGroup W] [Module K W] {Q : QuadraticForm K V}
  {Q₂ : QuadraticForm K W}

theorem orth_layer_count (hodd : Odd (Nat.card K)) (π : X →* (V ≃ₗ[K] V))
    (hker : π.ker ≤ Subgroup.center X) {Fund : Set (Subgroup X)}
    (hperf : ∀ R ∈ Fund, ⁅R, R⁆ = R) (hmap : ∀ R ∈ Fund, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ Fund, R.map π = L) {R₀ : Subgroup X} (hR₀ : R₀ ∈ Fund)
    (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) {N : ℕ}
    (hN : Nat.card {S : Subgroup X // S ∈ Fund ∧ Commutes S R₀} = N) :
    2 * Nat.card (OFrame Q₂) +
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      N * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  have : Finite V := Module.finite_of_finite K
  obtain ⟨i, F₀, hF₀, -⟩ := hmap R₀ hR₀
  have hcard := card_commuting_map π hker hperf hmap hsurj R₀
  rw [hN, hF₀] at hcard
  obtain ⟨F₁, ι, hι, hinj, hrange⟩ := exists_frame_perp_emb e
  have h1 := two_mul_card_frames_perp hodd F₀
  rw [card_frames_perp_conj hodd F₀ F₁, card_frames_perp F₁ ι hι hinj hrange, ← hcard] at h1
  exact h1

end Count

end CFSG.ClassicalInvolution.RouteD.NonClassical
