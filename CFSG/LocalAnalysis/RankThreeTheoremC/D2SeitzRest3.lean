module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LieAlt3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.RoadmapAll

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def IsD2SeitzRankThree (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    (d = .twistedA 3 q ∨ d = .B 3 q ∨ d = .B 4 q)

@[expose] def IsD2SeitzRest (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  (p = 3 ∧ ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d = .A 1 q) ∨
    (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d = .A 2 q) ∨ d = .tits)) ∨
  (p = 5 ∧ (d = .tits ∨ d = .suzuki 2))

theorem isD2SeitzException_iff {p : ℕ} {d : TauCeti.LieTypeIndex} :
    IsD2SeitzException p d ↔ IsD2SeitzRest p d ∨ IsD2SeitzRankThree p d := by
  constructor
  · rintro (⟨rfl, h | h | ⟨q, hq2, hq1, hd⟩ | ⟨q, hq2, hq1, hd | hd⟩ | h⟩ | ⟨rfl, h⟩)
    · exact .inl (.inl ⟨rfl, .inl h⟩)
    · exact .inl (.inl ⟨rfl, .inr (.inl h)⟩)
    · exact .inr ⟨rfl, q, hq2, hq1, .inl hd⟩
    · exact .inr ⟨rfl, q, hq2, hq1, .inr (.inl hd)⟩
    · exact .inr ⟨rfl, q, hq2, hq1, .inr (.inr hd)⟩
    · exact .inl (.inl ⟨rfl, .inr (.inr h)⟩)
    · exact .inl (.inr ⟨rfl, h⟩)
  · rintro (⟨⟨rfl, h | h | h⟩ | ⟨rfl, h⟩⟩ | ⟨rfl, q, hq2, hq1, hd | hd | hd⟩)
    · exact .inl ⟨rfl, .inl h⟩
    · exact .inl ⟨rfl, .inr (.inl h)⟩
    · exact .inl ⟨rfl, .inr (.inr (.inr (.inr h)))⟩
    · exact .inr ⟨rfl, h⟩
    · exact .inl ⟨rfl, .inr (.inr (.inl ⟨q, hq2, hq1, hd⟩))⟩
    · exact .inl ⟨rfl, .inr (.inr (.inr (.inl ⟨q, hq2, hq1, .inl hd⟩)))⟩
    · exact .inl ⟨rfl, .inr (.inr (.inr (.inl ⟨q, hq2, hq1, .inr hd⟩)))⟩

@[expose] def D2SeitzExcRest3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzRest p d.1

theorem d2SeitzExc3_of_rest3 (h3 : KFactSeitzRankThreeExceptions) (h : D2SeitzExcRest3 G) :
    D2SeitzExc3 G := by
  intro d hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  rcases isD2SeitzException_iff.1 hpp with hr | ⟨hp3, hq⟩
  · exact h d hS hD1 M hM ha hb p hp hr P A H R hMP hesc hmax Rbar K hRbar hK he
  · subst hp3
    exact hK.false_of_three_le_pRank (h3 K d hq he)

theorem d2SeitzExcRest3_of_seitzExc3 (h : D2SeitzExc3 G) : D2SeitzExcRest3 G :=
  fun d hS hD1 M hM ha hb p hp hpp =>
    h d hS hD1 M hM ha hb p hp (isD2SeitzException_iff.2 (.inl hpp))

end CFSG.LocalAnalysis.RankThreeTheoremC
