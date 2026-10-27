module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2IndexCases3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporSections

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

theorem d2IndexCase3_sporadic_of_section (hsec : SporSectionFacts3) {s : TauCeti.SporadicName}
    (hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)) :
    D2IndexCase3 G (.sporadic s) := by
  intro hS hD1 M hM ha hb p hp _ P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
  have hnonab : ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
      hK.component.2.2
  have e' : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group :=
    ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans QuotientGroup.quotientBot).trans e
  exact false_of_mem_sectionExcluded3 hsec hS.rank (primeComplementCore (G := H) p) hsimple hnonab
    hs e'

@[expose] def D2SporadicRest3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ s : TauCeti.SporadicName,
    s ∉ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName) →
    D2IndexCase3 G (.sporadic s)

theorem d2SporadicCase3_of_rest3 (hsec : SporSectionFacts3) (h : D2SporadicRest3 G) :
    D2SporadicCase3 G := by
  intro s
  by_cases hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)
  · exact d2IndexCase3_sporadic_of_section hsec hs
  · exact h s hs

theorem d2SporadicRest3_of_sporadicCase3 (h : D2SporadicCase3 G) : D2SporadicRest3 G :=
  fun s _ => h s

@[expose] def D2VacuousAt (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Sylow p X) (A X₀ K : Subgroup X),
    D2AlmostSimple p X R A X₀ K → Nonempty (K ≃* i.Group) → False

theorem d2IndexCaseAt3_of_vacuous {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h : ∀ p, Pp p → D2VacuousAt i p) : D2IndexCaseAt3 G i Pp := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  exact h p hpp _ Rbar _ _ K hK he

theorem d2IndexCaseAt3_of_indexCase3 {i : TauCeti.CFSGIndex} (h : D2IndexCase3 G i)
    (Pp : ℕ → Prop) : D2IndexCaseAt3 G i Pp :=
  fun hS hD1 M hM ha hb p hp _ => h hS hD1 M hM ha hb p hp trivial

theorem d2IndexCaseAt3_of_vac_cases {i : TauCeti.CFSGIndex} {Pp ZK : ℕ → Prop}
    (hZK : ∀ p, ZK p → D2VacuousAt i p)
    (h : D2IndexCaseAt3 G i fun p => Pp p ∧ ¬ ZK p) : D2IndexCaseAt3 G i Pp := by
  intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  by_cases hr : ZK p
  · exact hZK p hr _ Rbar _ _ K hK he
  · exact h hS hD1 M hM ha hb p hp ⟨hpp, hr⟩ P A H R hMP hesc hmax Rbar K hRbar hK he

end CFSG.LocalAnalysis.RankThreeTheoremC
