module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2IndexCases3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltCase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore HasPrimeConstraint)

variable {G : Type} [Group G] [Finite G]

@[expose] def D2CaseL2Square3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.exponent = 2 ∧ d.1 = .A 1 q) →
    D2IndexCaseAt3 G (.lie d) fun p => p = d.1.characteristic

@[expose] def D2CaseU33 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex,
    (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
    D2IndexCaseAt3 G (.lie d) fun p => p = d.1.characteristic

@[expose] def D2SeitzExc3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, D2IndexCaseAt3 G (.lie d) fun p => IsD2SeitzException p d.1

theorem d2IndexCaseAt3_lie_cross (hS : KFactSeitzRankTwo) (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt3 G (.lie d) fun p => p ≠ d.1.characteristic ∧ ¬ IsD2SeitzException p d.1 :=
  fun _ _ _ _ _ _ _ _ hp _ _ _ _ _ _ _ _ _ _ hK ⟨e⟩ => hK.false_of_seitz hS d e hp.1 hp.2

theorem d2IndexCaseAt3_lie_char_of (hrank : KFactLieCharRank) (hout : KFactLieCharOut)
    (hL2 : KFactLinTwoPrimeRank) (hL3 : KFactLinThreeCore) (hsq : D2CaseL2Square3 G)
    (hU3 : D2CaseU33 G) (d : TauCeti.ValidLieTypeIndex) :
    D2IndexCaseAt3 G (.lie d) fun p => p = d.1.characteristic := by
  intro hS hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  by_cases hsmall : IsD2LieCharSmall p d.1
  · have hRK := hK.sylow_le_of_not_dvd_card_outer (hout K d ⟨e⟩ p hK.prime hK.ne_two hsmall)
    obtain ⟨q, hqp, hq⟩ := hsmall
    rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
    · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with h1 | h2
      · have := hL2 K d ⟨e⟩ p hK.prime hK.ne_two ⟨q, hqp, h1, hd⟩
        have := hK.two_le_pRank_of_sylow_le hRK
        omega
      · exact hsq d ⟨q, h2, hd⟩ hS hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK
          ⟨e⟩
    · refine hK.not_le (hK.le_of_glbCore_eq_top (Rbar.subtype hRK).isPGroup' ?_
        (hL3 K d ⟨e⟩ p hK.prime hK.ne_two ⟨q, hqp, hq1, hd⟩ (Rbar.subtype hRK)))
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRK]
    · exact hU3 d ⟨q, hq1, hd⟩ hS hD1 M hM ha hb p hp hpc P A H R hMP hesc hmax Rbar K hRbar hK
        ⟨e⟩
  · exact hK.false_of_three_le_pRank (hrank K d ⟨e⟩ p hK.prime hK.ne_two hpc hsmall)

theorem d2LieCase3_of (hS : KFactSeitzRankTwo)
    (hchar : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt3 G (.lie d) fun p => p = d.1.characteristic)
    (hexc : D2SeitzExc3 G) : D2LieCase3 G := by
  intro d
  refine d2IndexCase3_of_cases (hchar d) ?_
  intro hS' hD1 M hM ha hb p hp hpp P A H R hMP hesc hmax Rbar K hRbar hK he
  by_cases hexcp : IsD2SeitzException p d.1
  · exact hexc d hS' hD1 M hM ha hb p hp hexcp P A H R hMP hesc hmax Rbar K hRbar hK he
  · exact d2IndexCaseAt3_lie_cross hS d hS' hD1 M hM ha hb p hp ⟨hpp, hexcp⟩ P A H R hMP hesc
      hmax Rbar K hRbar hK he

theorem d2AltCase3_of_twoMul
    (h : ∀ (p : ℕ) (hp : 5 ≤ 2 * p), D2IndexCase3 G (.alternating (2 * p) hp)) :
    D2AltCase3 G := by
  intro n hn hS hD1 M hM ha hb p hp _ P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  have hn2 : n = 2 * p := hK.eq_two_mul_of_alternating hn e
  subst hn2
  exact h p hn hS hD1 M hM ha hb p hp trivial P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩

@[expose] def D2AltNoConfig3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → TheoremD1 G → ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M → D2FullCoreAt G M →
    D2ThreeClauseAt G M → ∀ (p : ℕ) [Fact p.Prime], p ∈ rankThreeSigmaA G → 5 ≤ p →
    ∀ (P : Sylow p G) (A H : Subgroup G), IsCoreMaxLocal p P M → D2Escape p P M A H A →
    D2EscapeMax p P M A →
    ∀ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
      (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
      (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
      D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
        ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K →
      Nonempty (K ≃* alternatingGroup (Fin (2 * p))) → False

@[expose] def D2AltSixCase3 (G : Type) [Group G] [Finite G] : Prop :=
  D2IndexCaseAt3 G (.alternating 6 (by norm_num)) fun p => p = 3

theorem d2IndexCase3_alt_of (hNo : D2AltNoConfig3 G) (hA6 : D2AltSixCase3 G) (n : ℕ)
    (hn : 5 ≤ 2 * n) : D2IndexCase3 G (.alternating (2 * n) hn) := by
  intro hS hD1 M hM ha hb p hp _ P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  have hprime : p.Prime := hesc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hnp : 2 * n = 2 * p := hK.eq_two_mul_of_alternating hn e
  have hnp' : n = p := by omega
  subst hnp'
  rcases (show n = 3 ∨ 5 ≤ n by
      have := hprime.two_le
      have := hesc.ne_two
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hprime) (by norm_num)
      · exact Or.inr h) with h3 | h5
  · subst h3
    exact hA6 hS hD1 M hM ha hb 3 hp rfl P A H R hMP hesc hmax Rbar K hRbar hK ⟨e⟩
  · have hRA := hK.sylow_eq_of_alternating h5 e
    rw [hRbar] at hRA
    have hAR : A = R := hesc.A_eq_of_map_eq hRA
    subst hAR
    exact hNo hS hD1 M hM ha hb n hp h5 P A H hMP hesc hmax Rbar K hRbar hK ⟨e⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
