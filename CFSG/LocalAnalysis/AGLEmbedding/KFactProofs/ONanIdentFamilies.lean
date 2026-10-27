module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsFamilies
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem kFactSmallIdent_of_families (halt : SmallIdentAlt) (hcp : SmallIdentLieCharP)
    (hoff : SmallIdentLieOffChar) (hspor : ∀ s, SmallIdentSporAt s) : KFactSmallIdent := by
  intro K _ _ hs hnab hcat p hp hp2 T hT hΓ hr
  have hr' : Open.pRank p (⊤ : Subgroup K) ≤ 2 :=
    (CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp (⊤ : Subgroup K)).symm.le.trans hr
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
  | alternating n hn => exact halt K n hn ⟨e⟩ p hp hp2 T hT hΓ hr'
  | lie d =>
    by_cases hc : p = d.1.characteristic
    · exact hcp K hs hnab d ⟨e⟩ p hc hp hp2 T hT hΓ hr'
    · exact hoff K hs hnab d ⟨e⟩ p hc hp hp2 T hT hΓ hr'
  | sporadic s => exact hspor s K hs hnab ⟨e⟩ p hp hp2 T hT hΓ hr'

theorem kFactOneLieIdent_of_families (halt : OneLieIdentAlt) (hcp : OneLieIdentLieCharP)
    (hoff : OneLieIdentLieOffChar) (hspor : ∀ s, OneLieIdentSporAt s) : KFactOneLieIdent := by
  intro K _ _ hs hnab hcat p
  obtain ⟨i, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic q hq => exact (not_nonempty_mulEquiv_zmod hnab ⟨e⟩).elim
  | alternating n hn => exact halt K n hn ⟨e⟩ p
  | lie d =>
    by_cases hc : p = d.1.characteristic
    · exact hcp K hs hnab d ⟨e⟩ p hc
    · exact hoff K hs hnab d ⟨e⟩ p hc
  | sporadic s => exact hspor s K hs hnab ⟨e⟩ p

theorem smallIdentLieOffChar_of_gen (hg : OffCharGen) : SmallIdentLieOffChar := by
  intro K _ _ hs hnab d he p hpc hp hp2 T hT hΓ _
  by_cases h3 : p = 3 ∧ IsLinThreeFourIndex d
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3.1, Or.inl ⟨d, h3.2, he⟩⟩)))
  by_cases h5 : p = 5 ∧ d.1 = .tits
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h5.1, Or.inl ⟨d, h5.2, he⟩⟩))))
  exact absurd (hg K hs hnab d he p hp hp2 hpc T hT h3 h5) hΓ

theorem oneLieIdentLieOffChar_of_gen (hg : OffCharGen) (ha : OffCharAut) :
    OneLieIdentLieOffChar := by
  intro K _ _ hs hnab d he p hpc hp hp2 T hT hΓ hAut
  by_cases h3 : p = 3 ∧ IsLinThreeFourIndex d
  · exact absurd (ha K hs hnab d he p (Or.inl h3)) hAut
  by_cases h5 : p = 5 ∧ d.1 = .tits
  · exact absurd (ha K hs hnab d he p (Or.inr h5)) hAut
  exact absurd (hg K hs hnab d he p hp hp2 hpc T hT h3 h5) hΓ

end CFSG.AGLEmbedding
