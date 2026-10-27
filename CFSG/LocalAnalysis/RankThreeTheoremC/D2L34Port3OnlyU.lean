module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Port3Only
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3LeafU
import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3A6
import CFSG.LocalAnalysis.AGLEmbeddingD2.L34OnlyThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2OnlyL34At3U {G : Type} [Group G] [Finite G] (P : Sylow 3 G) (M : Subgroup G) :
    Prop :=
  ∀ A' H' R' : Subgroup G, D2Escape 3 P M A' H' R' →
    ∀ (Rbar' : Sylow 3 (H' ⧸ primeComplementCore (G := H') 3))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') 3)),
      (Rbar' : Subgroup _) = (R'.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3)) →
      D2AlmostSimple 3 (H' ⧸ primeComplementCore (G := H') 3) Rbar'
        ((A'.subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3)))
        (((H' ⊓ M).subgroupOf H').map (QuotientGroup.mk' (primeComplementCore 3))) K' →
      ∃ d' : TauCeti.ValidLieTypeIndex, IsL34Index d' ∧
        Nonempty (K' ≃* (TauCeti.CFSGIndex.lie d').Group)

theorem d2OnlyL34At3U_of (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (h3 : KFactSeitzRankThreeExceptions) (hA6 : D2AltSixCase3U G) (hThree : D2U3Three3U G)
    (hL28 : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3U G (.lie d) fun p => IsD2SeitzLTwoEight p d.1)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2IndexCaseAt3U G (.lie d) fun p => p = 3)
    (hSpor : ∀ s : TauCeti.SporadicName, D2IndexCaseAt3U G (.sporadic s) fun p => p = 3)
    (hSet : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} (hMP : IsCoreMaxLocal 3 P M) : D2OnlyL34At3U P M := by
  intro A H R hesc Rbar K hRbar hK
  exact hK.exists_l34_of_cases hrank hS.seitzCross h3
    (fun _ he => hA6 hSet hD1 M hM ha hb 3 hp rfl P A H R hMP hesc Rbar K hRbar hK he)
    (fun d hd hchar he => hThree d hd hSet hD1 M hM ha hb 3 hp ⟨hchar, rfl⟩ P A H R hMP hesc
      Rbar K hRbar hK he)
    (fun d hd he => hL28 d hSet hD1 M hM ha hb 3 hp hd P A H R hMP hesc Rbar K hRbar hK he)
    (fun d hd he => hTits d hd hSet hD1 M hM ha hb 3 hp rfl P A H R hMP hesc Rbar K hRbar hK
      he)
    fun s he => hSpor s hSet hD1 M hM ha hb 3 hp rfl P A H R hMP hesc Rbar K hRbar hK he
theorem d2SporadicThree3U_of (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (h : D2PairStrongThree3CompU G)
    (s : TauCeti.SporadicName) : D2IndexCaseAt3U G (.sporadic s) fun p => p = 3 := by
  by_cases hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)
  · exact d2IndexCaseAt3U_of_indexCase3U (d2IndexCase3U_sporadic_of_section hK.sections hs) _
  · refine d2IndexCaseAt3U_of_vac_cases (Pp := fun p => p = 3)
      (ZK := fun p => (s, p) ∉ d2SporadicOpenPairs3) (hK.sporVacuous s hs) ?_
    intro hS hD1 M hM ha hb p hp hpp P A H R hMP hesc Rbar K hRbar hK' he
    obtain ⟨rfl, hout⟩ := hpp
    rcases d2SporadicOpenPairs3_three (s, 3) (not_not.1 hout) rfl with hrow | hm
    · exact (hrows s 3 hrow _ Rbar _ _ K hK' he).elim
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hm
      exact d2IndexCaseAt3U_of_pair (fun _ hp => hp) (d2PairAt_of_maximal hM11) hK.eightFour
        hK.noXBlock3 (d2IndexCaseStrongAt3U_of_pairStrongCompU (fun _ hp => hp)
          (d2PairAt_of_maximal hM11) (d2SolvableAt_of_maximal hM11) (d2AutomizerAt_m11 hM11 hM11I)
          (d2SylowNineAt_m11 hM11) h) hS hD1 M hM ha hb 3 hp rfl P A H R hMP hesc Rbar K
        hRbar hK' he
theorem d2OnlyL34At3U_of_pairStrongCompU (hK : D2KFactLeaves)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p)
    (hT3 : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2VacuousAt (.lie d) 3)
    (hM11 : KFactM11Three) (hM11I : KFactM11ThreeIrr) (hK4 : KFactSylowThreeAbelian)
    (h : D2PairStrongThree3CompU G) (hSet : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} (hMP : IsCoreMaxLocal 3 P M) :
    D2OnlyL34At3U P M :=
  d2OnlyL34At3U_of hK.lieCharRank hK.seitzRankTwo hK.seitzRankThree
    (d2AltSixCase3U_of_strong hK.eightFour hK.noXBlock3
      (d2IndexCaseStrongAt3U_of_pairStrongCompU (fun _ hp => hp) d2PairAt_altSix d2SolvableAt_altSix
        d2AutomizerAt_altSix d2SylowNineAt_altSix h))
    (d2U3Three3U_of_strong hK.eightFour hK.noXBlock3 (d2U3ThreeStrong3U_of_pairStrongCompU h))
    (fun d => d2IndexCaseAt3U_of_pair (fun _ hp => hp.1) (d2PairAt_l28 d) hK.eightFour
      hK.noXBlock3 (d2L28Strong3U_of_pairStrongCompU hK.catalogSchreier hK4 h d))
    (fun d hd => d2IndexCaseAt3U_of_vacuous fun p hp => by rw [hp]; exact hT3 d hd)
    (d2SporadicThree3U_of hK hrows hM11 hM11I h) hSet hD1 hM ha hb hp hMP
end CFSG.LocalAnalysis.RankThreeTheoremC
