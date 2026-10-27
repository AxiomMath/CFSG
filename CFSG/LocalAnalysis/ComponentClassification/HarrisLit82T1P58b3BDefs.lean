module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bCl

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

namespace P58b3

@[expose] def Harris82Lemma58bThreeRowAt (τ : StatedLieTag) (n f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z₁ z₂ : G), orderOf z₁ = 2 → orderOf z₂ = 2 → z₁ ≠ z₂ →
    z₁ * z₂ = z₂ * z₁ → ∀ L₁ L₂ K : Subgroup G,
    IsSolvableTwoComponentIn L₁ (centralizer {z₁} ⊓ centralizer {z₂}) →
    (IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∨
      IsSolvableTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂})) →
    z₁ ∈ L₁ → z₂ ∈ L₂ → Nonempty (↥L₁ ⧸ pPrimeCore 2 ↥L₁ ≃* SL(2, ZMod 3)) →
    IsTwoComponentIn K (centralizer {z₁}) → GH74.GLS.oPrimeResidualOf 2 L₁ ≤ K →
    GH74.GLS.oPrimeResidualOf 2 L₂ ≤ K →
    centralizer {z₁} ⊓ centralizer {z₂} ≤ normalizer (K : Set G) →
    ∀ hz₂K : z₂ ∈ K, (QuotientGroup.mk ⟨z₂, hz₂K⟩ : ↥K ⧸ pPrimeCore 2 ↥K) ∉
      center (↥K ⧸ pPrimeCore 2 ↥K) →
    Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) τ n 3 f →
      (∃ m : ℕ, IsCoverOf .POmegaOdd m 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      ((IsTwoComponentIn L₂ (centralizer {z₁} ⊓ centralizer {z₂}) ∧
          ∃ (τ' : StatedLieTag) (n' : ℕ),
            Blueprint.LieModel (↥L₂ ⧸ Open.fusionZStar ↥L₂) τ' n' 3 1) →
        ∃ m : ℕ, Odd m ∧ 5 ≤ m ∧ IsCoverOf .POmegaOdd m 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K)) ∧
      (Nonempty (↥L₂ ⧸ pPrimeCore 2 ↥L₂ ≃* SL(2, ZMod 3)) →
        IsCoverOf .POmegaOdd 3 3 1 2 (↥K ⧸ pPrimeCore 2 ↥K))

theorem harris82Lemma58bThreeRow_of_at {τ : StatedLieTag} {n : ℕ}
    (h : ∀ f : ℕ, 1 ≤ f → Harris82Lemma58bThreeRowAt τ n f) : Harris82Lemma58bThreeRow τ n := by
  intro G _ _ z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z f hm
  exact h f (P58b.admissible_of_lieModel hm).2.1 G z₁ z₂ hz₁ hz₂ hne hc L₁ L₂ K hL₁ hL₂ hz₁L hz₂L
    he₁ hKc hO₁ hO₂ hN hz₂K hz₂Z hm

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
