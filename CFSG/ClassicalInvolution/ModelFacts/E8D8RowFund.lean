module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthTransport

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.RouteD.NonClassical (two_mul_card_frames_range)

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem card_fundSet_mul (hodd : Odd (Nat.card K)) :
    Nat.card (fundSet Q) * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      2 * Nat.card (OFrame Q) := by
  classical
  have : Finite V := Module.finite_of_finite K
  let _ : Fintype (fundSet Q) := Fintype.ofFinite _
  let g : OFrame Q → fundSet Q := fun F => ⟨F.La.range, F.La (-1), IsFundamental.of_frame F⟩
  have hg : Function.Surjective g := by
    rintro ⟨L, i, F, rfl, -⟩
    exact ⟨F, rfl⟩
  have hfib : ∀ S : fundSet Q, 2 * Nat.card {F : OFrame Q // g F = S} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
    intro S
    obtain ⟨F₁, hF₁⟩ := hg S
    have e : {F : OFrame Q // g F = S} ≃ {F : OFrame Q // F.La.range = F₁.La.range} :=
      { toFun := fun F => ⟨F.1, (congrArg Subtype.val F.2).trans
          (congrArg Subtype.val hF₁).symm⟩
        invFun := fun F => ⟨F.1, Subtype.ext (F.2.trans (congrArg Subtype.val hF₁))⟩
        left_inv := fun F => rfl
        right_inv := fun F => rfl }
    rw [Nat.card_congr e]
    exact two_mul_card_frames_range hodd F₁
  have hsum : Nat.card (OFrame Q) = ∑ S : fundSet Q, Nat.card {F : OFrame Q // g F = S} := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv g)]
  rw [hsum, Finset.mul_sum, Finset.sum_congr rfl fun S _ => hfib S, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]

theorem card_fund_mul_of_central {X : Type} [Group X] (hodd : Odd (Nat.card K))
    (π : X →* (V ≃ₗ[K] V)) (hker : π.ker ≤ Subgroup.center X) {Fund : Set (Subgroup X)}
    (hperf : ∀ R ∈ Fund, ⁅R, R⁆ = R) (hmap : ∀ R ∈ Fund, R.map π ∈ fundSet Q)
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ Fund, R.map π = L) :
    Nat.card Fund * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) =
      2 * Nat.card (OFrame Q) := by
  have hbij : Nat.card Fund = Nat.card (fundSet Q) := by
    refine Nat.card_eq_of_bijective (fun R => ⟨R.1.map π, hmap _ R.2⟩) ⟨?_, ?_⟩
    · intro R₁ R₂ h
      exact Subtype.ext (ModelFacts.eq_of_map_eq_of_isPerfect π hker (hperf _ R₁.2)
        (hperf _ R₂.2) (congrArg Subtype.val h))
    · rintro ⟨L, hL⟩
      obtain ⟨R, hR, rfl⟩ := hsurj L hL
      exact ⟨⟨R, hR⟩, rfl⟩
  rw [hbij]
  exact card_fundSet_mul hodd

end CFSG.ClassicalInvolution.ModelFacts.E8D8
