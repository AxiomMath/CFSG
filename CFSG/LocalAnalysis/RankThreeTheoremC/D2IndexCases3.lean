module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Component
import CFSG.LocalAnalysis.AGLEmbeddingD2.IndexCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2IndexCaseAt3 (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex)
    (Pp : ℕ → Prop) : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, Pp p → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R → D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* i.Group) → False

@[expose] def D2IndexCase3 (G : Type) [Group G] [Finite G] (i : TauCeti.CFSGIndex) : Prop :=
  D2IndexCaseAt3 G i fun _ => True

theorem d2ComponentCaseMax3_of_indexCases3 (h : ∀ i, D2IndexCase3 G i) :
    D2ComponentCaseMax3 G := by
  intro hS hD1 M hM ha hb p hp P A H R hMP hesc hmax Rbar K hRbar hK
  obtain ⟨i, hi⟩ := hK.catalog
  exact h i hS hD1 M hM ha hb p hp trivial P A H R hMP hesc hmax Rbar K hRbar hK hi

theorem d2IndexCase3_of_cases {i : TauCeti.CFSGIndex} {Pp : ℕ → Prop}
    (h₁ : D2IndexCaseAt3 G i Pp) (h₂ : D2IndexCaseAt3 G i fun p => ¬ Pp p) :
    D2IndexCase3 G i := by
  intro hS hD1 M hM ha hb p hp _ P A H R hMP hesc hmax Rbar K hRbar hK he
  by_cases hpp : Pp p
  · exact h₁ hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  · exact h₂ hS hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he

theorem d2AlmostSimple_false_of_cyclic {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X}
    {A X₀ K : Subgroup X} (h : D2AlmostSimple p X R A X₀ K) (q : ℕ) (hq : q.Prime)
    (e : K ≃* (TauCeti.CFSGIndex.cyclic q hq).Group) : False :=
  h.false_of_cyclic q hq e

theorem d2IndexCase3_cyclic (q : ℕ) (hq : q.Prime) : D2IndexCase3 G (.cyclic q hq) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK ⟨e⟩ => d2AlmostSimple_false_of_cyclic hK q hq e

@[expose] def D2AltCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (n : ℕ) (hn : 5 ≤ n), D2IndexCase3 G (.alternating n hn)

@[expose] def D2LieCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, D2IndexCase3 G (.lie d)

@[expose] def D2SporadicCase3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ s : TauCeti.SporadicName, D2IndexCase3 G (.sporadic s)

theorem d2ComponentCaseMax3_of_families3 (hA : D2AltCase3 G) (hL : D2LieCase3 G)
    (hS : D2SporadicCase3 G) : D2ComponentCaseMax3 G :=
  d2ComponentCaseMax3_of_indexCases3 fun i => match i with
    | .cyclic q hq => d2IndexCase3_cyclic q hq
    | .alternating n hn => hA n hn
    | .lie d => hL d
    | .sporadic s => hS s

end CFSG.LocalAnalysis.RankThreeTheoremC
