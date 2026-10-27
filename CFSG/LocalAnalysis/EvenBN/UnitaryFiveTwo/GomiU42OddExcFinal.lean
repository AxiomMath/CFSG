module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcRank
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcE6
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcE7
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcWire

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.false_of_oddLie_exceptional'
    (h : GomiU42Data X J D E a) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t ∈ chevalleyExceptionalTags) (hD : ChevalleyExceptionalModel ↥D t p f) : False := by
  have ht' : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 := by
    simpa [chevalleyExceptionalTags] using ht
  rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.false_of_oddLie_g2d4 hp hp2 (Or.inl rfl) hD
  · exact h.false_of_oddLie_F4E8 hp hp2 (Or.inl rfl) hD
  · exact h.false_of_oddLie_E6 hp hp2 hD
  · exact h.false_of_oddLie_E7 hp hp2 hD
  · exact h.false_of_oddLie_F4E8 hp hp2 (Or.inr rfl) hD
  · exact h.false_of_oddLie_twistedE6 hp hp2 hD
  · exact h.false_of_oddLie_g2d4 hp hp2 (Or.inr rfl) hD

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
