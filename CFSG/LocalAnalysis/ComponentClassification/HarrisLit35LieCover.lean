module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieFour
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Lie

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def Harris81Lemma35IdentFourCoverFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) →
    ((∃ k : ℕ,
        (Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL 4 p k ∨
          Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU 4 p k) ∧
        ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K))) ∧
        (IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L) ∨
          IsSLTwoOver (p ^ (2 * k)) (↥L ⧸ pPrimeCore 2 ↥L))) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n 2 f) ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .J2 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .HS) →
    L35.Concl p v L K

theorem harris81Lemma35IdentCoverFact_of_four (hF : Harris81Lemma35IdentFourCoverFact) :
    Harris81Lemma35IdentCoverFact := by
  intro G _ _ p w v L K h halt hcase
  apply hF G p w v L K h halt
  rcases hcase with ⟨n, k, hn, hm, hne⟩ | hrest
  · obtain ⟨rfl, hsl⟩ := h.four_of_partialCover hn hm
    exact Or.inl ⟨k, hm, hne, hsl⟩
  · exact Or.inr hrest

end CFSG.ComponentClassification.HarrisLit
