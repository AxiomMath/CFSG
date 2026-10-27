module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank620Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open CFSG.LocalAnalysis.RankThreeTheoremC

@[expose] def KFactCampbellBlock : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X K R P : Subgroup A),
    X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X →
    K ≤ X → X ≤ normalizer (K : Set A) → ⁅K, K⁆ = K → X = K ⊔ pCoreOf 2 X →
    (∃ f : ↥K →* GL32, Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : A) ∈ pCoreOf 2 X) →
    R ≤ X → IsPGroup 2 R → ¬ 2 ∣ (R.subgroupOf X).index →
    R ≤ P → P ≤ X → (P.subgroupOf X).index = 7 →
    X ⊓ centralizer ((omegaCenter R : Subgroup A) : Set A) ≤ P →
    (∀ Q₀ : Subgroup A, Q₀ ≤ pCoreOf 2 P → Q₀ ≠ ⊥ →
      (Q₀.subgroupOf (pCoreOf 2 P)).Characteristic → ¬ X ≤ normalizer (Q₀ : Set A)) →
    ∃ A₀ B₀ : Subgroup A, A₀ ≤ B₀ ∧ B₀ ≤ omegaCenter (K ⊓ pCoreOf 2 X) ∧
      X ≤ normalizer (A₀ : Set A) ∧ X ≤ normalizer (B₀ : Set A) ∧
      K ≤ centralizer (A₀ : Set A) ∧
      (∀ w ∈ K ⊓ pCoreOf 2 X, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ B₀) ∧
      A₀.relIndex B₀ = 8 ∧
      ∀ g ∈ X, (∀ u ∈ B₀, g * u * g⁻¹ * u⁻¹ ∈ A₀) → g ∈ pCoreOf 2 X

theorem kFactCampbell_of_kFactCampbellBlock (h : KFactCampbellBlock) : KFactCampbell := by
  intro A _ _ X K R P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  obtain ⟨A₀, B₀, hAB, hBW, hXA, hXB, hKA, hKW, hidx, hker⟩ :=
    h A X K R P h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  exact ⟨A₀, B₀, hAB, hBW, hXA, hXB, hKA, fun w hw => hKW w (omegaCenter_le _ hw), hidx, hker⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614
