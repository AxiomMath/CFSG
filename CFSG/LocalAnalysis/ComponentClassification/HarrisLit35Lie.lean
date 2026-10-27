module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35LieOdd
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Spor

public section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.Assembly.LowTwoRank

@[expose] def Harris81Lemma35IdentCoverFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (w v : G) (L K : Subgroup G),
    L35.Config G p w v L K → ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K) →
    ((∃ n k : ℕ, 2 ≤ n ∧
        (Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL (2 * n) p k ∨
          Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU (2 * n) p k) ∧
        ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)))) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n 2 f) ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .J2 ∨
      Blueprint.NativeSporadic.IsSporadic (↥K ⧸ Open.fusionZStar ↥K) .HS) →
    L35.Concl p v L K

theorem harris81Lemma35IdentResidFact_of_cover
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hC : Harris81Lemma35IdentCoverFact) : Harris81Lemma35IdentResidFact := by
  intro G _ _ p w v L K h halt hcase
  have hlie : ∀ {t : StatedLieTag} {n r f : ℕ},
      Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n r f →
      (∃ n k : ℕ, 2 ≤ n ∧
        (Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSL (2 * n) p k ∨
          Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) .PSU (2 * n) p k) ∧
        ordProj[2] (Nat.card ↥(center (↥K ⧸ pPrimeCore 2 ↥K))) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (↥K ⧸ Open.fusionZStar ↥K)))) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n 2 f) :=
    fun {t n r f} hL => by
      by_cases hr2 : r = 2
      · subst hr2
        exact Or.inr ⟨t, n, f, hL⟩
      · exact Or.inl (h.partialCover_of_oddLie hGLS hGA hr2 hL)
  apply hC G p w v L K h halt
  rcases hcase with ⟨t, n, r, f, hm⟩ | hex | hM | hJ | hH
  · have hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n r f := by
      refine Or.inl ⟨?_, hm⟩
      cases t <;> first | decide | exact hm.2.elim
    rcases hlie hL with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · have key : ∃ (t : StatedLieTag) (r f : ℕ),
        Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t 0 r f := by
      rcases hex with ⟨t, r, f, ht, hm⟩ | ⟨t, r, f, ht, hm⟩ | ⟨r, f, hm⟩
      · exact ⟨t, r, f, Or.inr (Or.inl ⟨rfl, ht, hm⟩)⟩
      · exact ⟨t, r, f, Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩))⟩
      · exact ⟨.twistedB2, r, f, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩))⟩
    obtain ⟨t, r, f, hL⟩ := key
    rcases hlie hL with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl hM))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hJ)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hH)))

end CFSG.ComponentClassification.HarrisLit
