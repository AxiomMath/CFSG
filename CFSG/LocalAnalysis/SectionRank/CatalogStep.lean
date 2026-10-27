module

public import CFSG.LocalAnalysis.SectionRank.G2OddCover
public import CFSG.LocalAnalysis.SectionRank.SQTKTransport

public section

namespace CFSG.SectionRank

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def CatalogStepConclusion (L : Type) [Group L] : Prop :=
  (Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3) ∧
    ∀ (A : Subgroup L) [A.Normal], A ≤ Subgroup.center L → IsStronglyQuasithin (L ⧸ A)

theorem catalog_exceptional_odd
    {L : Type} [Group L] [Finite L] (_hL : IsQuasisimple L)
    (hSQT : IsStronglyQuasithin L) (_hodd : Odd (Nat.card (Subgroup.center L)))
    (h : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((∃ t ∈ chevalleyExceptionalTags,
          ChevalleyExceptionalModel (L ⧸ Subgroup.center L) t p f) ∨
        ReeTitsModel (L ⧸ Subgroup.center L) .twistedG2 p f)) :
    CatalogStepConclusion L := by
  exfalso
  obtain ⟨p, f, hp, hp2, hmod⟩ := h
  obtain ⟨hche, hree⟩ := exceptional_odd_central_quotient_exclusion (f := f) hSQT
    (Subgroup.center L) le_rfl hp hp2
  rcases hmod with ⟨t, ht, hm⟩ | hm
  · exact hche t ht hm
  · exact hree hm

theorem catalogStepConclusion_of {L : Type} [Group L] [Finite L] (hSQT : IsStronglyQuasithin L)
    (hZ : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3)
    (hS : IsStronglyQuasithin (L ⧸ Subgroup.center L)) : CatalogStepConclusion L := by
  refine ⟨hZ, fun A _ hA => ?_⟩
  have hdvd : Nat.card A ∣ Nat.card (Subgroup.center L) := Subgroup.card_dvd_of_le hA
  have hA13 : Nat.card A = 1 ∨ Nat.card A = 3 := by
    rcases hZ with h | h
    · rw [h] at hdvd
      exact Or.inl (Nat.dvd_one.1 hdvd)
    · rw [h] at hdvd
      exact (Nat.dvd_prime Nat.prime_three).1 hdvd
  rcases hA13 with h1 | h3
  · obtain rfl : A = ⊥ := Subgroup.eq_bot_of_card_eq A h1
    exact isStronglyQuasithin_of_mulEquiv (QuotientGroup.quotientBot) hSQT
  · have hZ3 : Nat.card (Subgroup.center L) = 3 := by
      rcases hZ with h | h
      · rw [h, h3] at hdvd; exact absurd hdvd (by decide)
      · exact h
    obtain rfl : A = Subgroup.center L :=
      Subgroup.eq_of_le_of_card_ge hA (by rw [hZ3, h3])
    exact hS

end CFSG.SectionRank
