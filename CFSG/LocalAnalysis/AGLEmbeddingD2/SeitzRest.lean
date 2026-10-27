module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Seitz

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

theorem D2IndexCaseAt.mono {i : TauCeti.CFSGIndex} {Pp Qq : ℕ → Prop} (h : D2IndexCaseAt i Qq)
    (hPQ : ∀ p, Pp p → Qq p) : D2IndexCaseAt i Pp := by
  intro G _ _ hglob hD1 p hp
  exact h G hglob hD1 p (hPQ p hp)

theorem seitzRest_cases {d : TauCeti.ValidLieTypeIndex} {p : ℕ}
    (h : ((IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5)) ∧ ¬ (d.1 = .tits ∧ p = 3)) :
    (IsL34Index d ∧ p = 3) ∨ (d.1 = .suzuki 2 ∧ p = 5) := by
  obtain ⟨⟨⟨hexc, hrank⟩, hl28, ht5⟩, ht3⟩ := h
  rcases hexc with ⟨rfl, h3⟩ | ⟨rfl, h5⟩
  · rcases h3 with ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ |
      ⟨q, hq2, hq1, hd⟩ | hd
    · exact absurd ⟨rfl, q, hq2, hq3, hd⟩ hl28
    · exact Or.inl ⟨⟨q, hq2, hq2', hd⟩, rfl⟩
    · exact absurd ⟨rfl, q, hq2, hq1, Or.inl hd⟩ hrank
    · exact absurd ⟨rfl, q, hq2, hq1, Or.inr hd⟩ hrank
    · exact absurd ⟨hd, rfl⟩ ht3
  · rcases h5 with hd | hd
    · exact absurd ⟨hd, rfl⟩ ht5
    · exact Or.inr ⟨hd, rfl⟩

theorem d2SeitzRest_of_l34_sz (hO : KFactL34Outer) (hI : KFactL34Inner) (hβ : D2L34BetaCase)
    (hOnly : D2OnlyL34Three) (h84 : Asc81bEightFour) (hD2 : D1NoXBlock) (hS : D2PairStrongThree)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2IndexCaseAt (.lie d) fun p => p = 5)
    (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt (.lie d) fun p => ((IsD2SeitzException p d.1 ∧ ¬ (p = 3 ∧
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
          (d.1 = .twistedA 3 q ∨ d.1 = .B 3 q ∨ d.1 = .B 4 q))) ∧
        ¬ CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1 ∧
        ¬ (d.1 = .tits ∧ p = 5)) ∧ ¬ (d.1 = .tits ∧ p = 3) := by
  intro G _ _ hglob hD1 p hp
  rcases seitzRest_cases hp with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · exact d2IndexCaseAt_l34_three hO hI hβ hOnly h84 hD2 hS d hd G hglob hD1 3 rfl
  · exact hSz d hd G hglob hD1 5 rfl

end CFSG.AGLEmbeddingD2
