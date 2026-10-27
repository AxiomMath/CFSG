module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

abbrev u3X₀ (L K : Subgroup G) : Subgroup G :=
  ⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆

structure U3MinCounter (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) : Prop where
  hyp : BenderHyp G L
  three_le : 3 ≤ f
  iso : Nonempty (rankTwoQuot L ≃* PSU3 2 f)
  ih : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → ∀ L' : Subgroup H,
    BenderHyp H L' → ∀ f' : ℕ, 3 ≤ f' → Nonempty (rankTwoQuot L' ≃* PSU3 2 f') → False

theorem u3Res_of_u3MinCounter
    (h : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ), U3MinCounter G L f → False) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), BenderHyp G L → ∀ f : ℕ, 3 ≤ f →
      Nonempty (rankTwoQuot L ≃* PSU3 2 f) → False := by
  suffices H : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ L : Subgroup G, BenderHyp G L → ∀ f : ℕ, 3 ≤ f →
        Nonempty (rankTwoQuot L ≃* PSU3 2 f) → False by
    intro G _ _ L hL f hf he
    exact H _ G rfl L hL f hf he
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ hn L hL f hf he
    exact h G L f ⟨hL, hf, he, fun H _ _ hH L' hL' f' hf' he' =>
      ih _ (hn ▸ hH) H rfl L' hL' f' hf' he'⟩

end CFSG.ComponentClassification.GMS78
