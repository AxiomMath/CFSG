module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporOpen3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

@[expose] def d2HeisFamily3 : TauCeti.CFSGIndex → ℕ → Prop :=
  fun i p => (i = .sporadic .McL ∧ p = 5) ∨ (i = .sporadic .J4 ∧ p = 11)

@[expose] def d2TorusFamily3 : TauCeti.CFSGIndex → ℕ → Prop :=
  fun i p => (∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits) ∧ p = 5

@[expose] def d2VacuousFamily3 : TauCeti.CFSGIndex → ℕ → Prop := fun i p =>
  ((∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits) ∧ p = 3) ∨
  ∃ s, i = .sporadic s ∧ ((s, p) ∈ d2SporadicRows3 ∨
    (s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) ∧
      (s, p) ∉ d2SporadicOpenPairs3))

@[expose] def IsD2SeitzLeaf3 (p : ℕ) (d : TauCeti.LieTypeIndex) : Prop :=
  p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d = .A 2 q

theorem d2HeisFamily3_borel (hMcL : D2HeisLocalAt (.sporadic .McL) fun p => p = 5)
    (hJ4 : D2HeisLocalAt (.sporadic .J4) fun p => p = 11) :
    ∀ i, D2HeisBorelAt i (d2HeisFamily3 i) := by
  intro i X _ _ p hp R A X₀ K hK he
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact d2HeisBorelAt_of_local hMcL X 5 rfl R A X₀ K hK he
  · exact d2HeisBorelAt_of_local hJ4 X 11 rfl R A X₀ K hK he

theorem d2TorusFamily3_borel (hTits5 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
    D2TorusLocalAt (.lie d) fun p => p = 5) : ∀ i, D2TorusBorelAt i (d2TorusFamily3 i) := by
  intro i
  by_cases hi : ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ d.1 = .tits
  · obtain ⟨d, rfl, hd⟩ := hi
    exact fun X _ _ p hp R A X₀ K hK he =>
      d2TorusBorelAt_of_local (hTits5 d hd) X p hp.2 R A X₀ K hK he
  · exact fun X _ _ p hp => absurd hp.1 hi

theorem d2VacuousFamily3_vacuous (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 →
      D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hvac : D2SporadicVacuous3) : ∀ i p, d2VacuousFamily3 i p → D2VacuousAt i p := by
  rintro i p (⟨⟨d, rfl, hd⟩, rfl⟩ | ⟨s, rfl, hs | ⟨hs5, hs⟩⟩)
  · exact hT3 d hd
  · exact hrows s p hs
  · exact hvac s hs5 p hs

end CFSG.LocalAnalysis.RankThreeTheoremC
