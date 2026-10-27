module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporOpen3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2Families3Heis
public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransCase
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2HSFiveNonBorel3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ p ∈ rankThreeSigmaA G, p = 5 → ∀ (P : Sylow p G) (A H R : Subgroup G),
    IsCoreMaxLocal p P M → D2Escape p P M A H R → D2EscapeMax p P M R →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ≠
        Subgroup.normalizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) → False

theorem d2HeisBorelFor_hs_five3 (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hU : D2HSFiveNonBorel3 G) (hS : Setting G) (hD1 : TheoremD1 G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (ha : D2FullCoreAt G M) (hb : D2ThreeClauseAt G M)
    (hp : 5 ∈ rankThreeSigmaA G) {P : Sylow 5 G} {A R : Subgroup G}
    (hMP : IsCoreMaxLocal 5 P M) (hmax : D2EscapeMax 5 P M R) :
    D2HeisBorelFor 5 P M A R (.sporadic .HS) :=
  fun H hesc Rbar K hRbar hK he => hloc.heisBorel rfl hK he (by
    by_contra hne
    exact hU hS hD1 M hM ha hb 5 hp rfl P A H R hMP hesc hmax Rbar K hRbar hK he hne)

theorem d2IndexCaseAt3_sporadic_five_of_rows (hvac : D2SporadicVacuous3) (hsec : SporSectionFacts3)
    (hrows : ∀ s p, (s, p) ∈ d2SporadicRows3 → D2VacuousAt (.sporadic s) p) :
    ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt3 G (.sporadic s) fun p => p = 5 := by
  intro s h1 h2
  by_cases hs : s ∈ ({.Fi22, .Fi23, .Fi24Prime, .B, .M} : Finset TauCeti.SporadicName)
  · exact d2IndexCaseAt3_of_indexCase3 (d2IndexCase3_sporadic_of_section hsec hs) _
  · refine d2IndexCaseAt3_of_vacuous fun p hp => ?_
    subst hp
    by_cases hmem : (s, 5) ∈ d2SporadicOpenPairs3
    · have key : ∀ x ∈ d2SporadicOpenPairs3, x.2 = 5 → x ≠ (TauCeti.SporadicName.HS, 5) →
          x ≠ (TauCeti.SporadicName.McL, 5) → x ∈ d2SporadicRows3 := by
        decide
      exact hrows s 5 (key (s, 5) hmem rfl (fun he => h1 (Prod.mk.inj he).1)
        (fun he => h2 (Prod.mk.inj he).1))
    · exact hvac s hs 5 hmem

theorem d2IndexCaseAt3_hs_five (hrank : KFactLieCharRank) (hS : KFactSeitzRankTwo)
    (hMS : D2HeisMSide3 G) (hCGT : AschbacherLocalCGTBlock) (hX : D1NoXBlock3 G)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5) (hU : D2HSFiveNonBorel3 G)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      D2TorusBorelAt (.lie d) fun p => p = 5)
    (hSzB : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      D2TransBorelAt (.lie d) fun p => p = 5)
    (hMcL : D2HeisBorelAt (.sporadic .McL) fun p => p = 5)
    (hSpor : ∀ s : TauCeti.SporadicName, s ≠ .HS → s ≠ .McL →
      D2IndexCaseAt3 G (.sporadic s) fun p => p = 5) :
    D2IndexCaseAt3 G (.sporadic .HS) fun p => p = 5 := by
  intro hSet hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  subst hpp
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hBfor := d2HeisBorelFor_hs_five3 (A := A) hloc hU hSet hD1 hM ha hb hp hMP hmax
  have hB := hBfor H hesc Rbar K hRbar hK he
  have hRQ := hMS hSet hD1 M hM ha hb 5 hp (by norm_num) P A H R hMP hesc hmax Rbar K hRbar hK hB
  have hcard : Nat.card R = 5 ^ 3 := by
    rw [← hesc.card_map_eq le_rfl, ← hRbar]
    exact hB.card
  have hRexp : ∀ r ∈ R, r ^ 5 = 1 := fun r hr => by
    by_contra hr5
    exact hesc.false_of_pow_eq_one hRbar ⟨r, hr, hr5⟩ hB.pow_eq_one
  refine hesc.false_of_heisBorelFor' hrank kFactLinThreeCore hS unitaryBorelKFacts
    (fun d hd => ?_) (fun s => ?_) hCGT (aglGlobal_of_setting hSet) (d1At_of_theoremD1 hD1 hp)
    (noXBlockFor_of_setting hX hSet) hmax le_rfl hRbar hB hRQ
  · intro H' h' Rbar' K' hRbar' hK' he'
    exfalso
    rcases hd with ⟨h53, -⟩ | ⟨-, hdt | hdz⟩
    · norm_num at h53
    · have hT := hTits d hdt _ 5 rfl Rbar' _ _ K' hK' he'
      have hcA := h'.card_A
      rw [h'.A_eq_of_map_eq (hRbar'.symm.trans hT.eq_A), hcard] at hcA
      norm_num at hcA
    · obtain ⟨zb, hB'⟩ := hSzB d hdz _ 5 rfl Rbar' _ _ K' hK' he'
      obtain ⟨b, hbR, hb⟩ := exists_pow_ne_one_of_map hRbar' hB'.exp
      exact hb (hRexp b hbR)
  · by_cases h1 : s = .HS
    · subst h1
      exact hBfor
    by_cases h2 : s = .McL
    · subst h2
      exact hMcL.for rfl
    · exact ((hSpor s h1 h2).for hSet hD1 hM ha hb hp rfl hMP hmax).heisBorelFor

end CFSG.LocalAnalysis.RankThreeTheoremC
