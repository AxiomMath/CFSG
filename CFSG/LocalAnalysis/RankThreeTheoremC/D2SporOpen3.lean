module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporNarrow3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

@[expose] def d2SporadicOpenPairs3 : List (TauCeti.SporadicName × ℕ) :=
  [(.M11, 3), (.McL, 5), (.J4, 11), (.HS, 5), (.J4, 3), (.J2, 3), (.He, 3), (.Ru, 3), (.Ru, 5),
    (.Co2, 5), (.Co3, 5), (.Th, 5), (.He, 7), (.ONan, 7)]

@[expose] def d2SporadicRows3 : List (TauCeti.SporadicName × ℕ) :=
  [(.J2, 3), (.He, 3), (.Ru, 3), (.Ru, 5), (.Co2, 5), (.Co3, 5), (.He, 7), (.ONan, 7), (.J4, 3),
    (.Th, 5)]

theorem d2SporadicOpenPairs3_cover : ∀ x ∈ d2SporadicOpenPairs3, x ∈ d2SporadicRows3 ∨
    x = (TauCeti.SporadicName.M11, 3) ∨ x = (TauCeti.SporadicName.McL, 5) ∨
    x = (TauCeti.SporadicName.J4, 11) ∨ x = (TauCeti.SporadicName.HS, 5) := by
  decide

@[expose] def D2SporadicOpen3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (s : TauCeti.SporadicName) (p : ℕ), (s, p) ∈ d2SporadicOpenPairs3 →
    D2IndexCaseAt3 G (.sporadic s) fun q => q = p

@[expose] def D2SporadicVacuous3 : Prop :=
  ∀ s : TauCeti.SporadicName,
    s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
    ∀ p : ℕ, (s, p) ∉ d2SporadicOpenPairs3 → D2VacuousAt (.sporadic s) p

theorem d2SporadicOpenPairs3_names (s : TauCeti.SporadicName) (p : ℕ)
    (h : (s, p) ∈ d2SporadicOpenPairs3) :
    s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) := by
  have key : ∀ x ∈ d2SporadicOpenPairs3,
      x.1 ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) := by
    decide
  exact key (s, p) h

theorem d2SporadicRest3_of_open3 (hvac : D2SporadicVacuous3) (h : D2SporadicOpen3 G) :
    D2SporadicRest3 G := by
  intro s hs
  refine d2IndexCaseAt3_of_vac_cases (Pp := fun _ => True)
    (ZK := fun p => (s, p) ∉ d2SporadicOpenPairs3) (hvac s hs) ?_
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  exact h s p (not_not.1 hpp.2) hS hD1 M hM ha hb p hp rfl P A H R hMP hesc hmax Rbar K hRbar
    hK he

theorem d2SporadicOpen3_of_rest3 (h : D2SporadicRest3 G) : D2SporadicOpen3 G :=
  fun s p hmem =>
    d2IndexCaseAt3_of_indexCase3 (h s (d2SporadicOpenPairs3_names s p hmem)) _

theorem d2SporadicOpen3_of_sporadicCase3 (h : D2SporadicCase3 G) : D2SporadicOpen3 G :=
  d2SporadicOpen3_of_rest3 (d2SporadicRest3_of_sporadicCase3 h)

end CFSG.LocalAnalysis.RankThreeTheoremC
