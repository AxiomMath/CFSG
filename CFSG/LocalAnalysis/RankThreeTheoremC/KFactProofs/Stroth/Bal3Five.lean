module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Comp
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

theorem kFactLemma212_five_le (hK : SchurMultiplierRankFact) :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (H : Type) [Group H] [Finite H],
      CFSG.AGLEmbedding.CatalogSimpleSections H → ∀ (P : Sylow p H) (z : H) (D : Subgroup H),
        Lemma212Config p P z D →
          HasPrimeConstraint (G := H) p ∨
            CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ := by
  intro p hp hp5 H _ _ hcat P z D hconf
  by_contra hno
  push_neg at hno
  obtain ⟨hcon, hQ⟩ := hno
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p ≠ 2 := by omega
  have hred := Lemma212Config.reduce hodd hconf
  obtain ⟨K, hKc⟩ := exists_isComponentOf_of_not_hasPrimeConstraint hp hcon
  have hz := hred.mem_pCore hQ
  have hnorm := hred.le_normalizer_component hz hKc
  have hdvd := hred.dvd_card_center_component hz hKc hnorm
  have hX : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) := hcat.quotient _
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hKc.2.2
  have hcatK : IsCatalogGroup (K ⧸ center K) :=
    hX K (center K) inferInstance hKc.2.2.2 hnonab
  have h4 := hK p hp hp5 K hKc.2.2 hcatK hdvd
  have hKX : CFSG.Open.pRank p (⊤ : Subgroup K) ≤
      CFSG.Open.pRank p (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p hp K.subtype
      K.subtype_injective]
    exact CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_top
  rw [hred.pRank_top] at hKX
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
