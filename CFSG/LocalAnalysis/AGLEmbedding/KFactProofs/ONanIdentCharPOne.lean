module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentCharPBasic
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutElemRank
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem pRank_top_mulAut_le_two_of_linTwo_sq {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p 2 d)
    (he : Nonempty (K ≃* CatGroup d)) : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨e⟩ := he
  obtain ⟨f⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt
    (MulAut.congr (e.trans f))]
  exact CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE =>
    kFactL2AutElemRank p 2 hp2 (by norm_num) E hE

theorem pRank_top_mulAut_le_two_of_unitary_one {K : Type} [Group K] [Finite K] {p : ℕ}
    [Fact p.Prime] {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d)
    (h1 : d.1.fieldExponent = 1) (he : Nonempty (K ≃* CatGroup d)) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 :=
  CFSG.SectionRank.pRank_le (Fact.out : p.Prime).one_lt fun E _ hE => by
    simpa [h1] using kFactUnitaryAutElemRank K p d hd he E hE

theorem oneLieIdentLieCharP (hC : CharPGen) : OneLieIdentLieCharP := by
  intro K _ _ hs hnab d he p hpc hp hp2 T hT hΓ hAut
  have : Fact p.Prime := ⟨hp⟩
  have hrank : IsRankOneLieIndex d.1 := by
    by_contra h
    exact hΓ (hC K hs hnab d he p hp hp2 hpc h T)
  obtain ⟨e⟩ := he
  rcases hrank with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨m, hd⟩
  · have hqp : q.p = p := by simpa [hd] using hpc.symm
    rcases (show q.exponent = 1 ∨ q.exponent = 2 ∨ 3 ≤ q.exponent by
      have := q.exponent_pos; omega) with h1 | h2 | h3
    · exact absurd (isCyclic_sylow_of_pRank_le_one hp hp2
        (CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank K d ⟨e⟩ p hp hp2 ⟨q, hqp, h1, hd⟩) T) hT
    · exact absurd (pRank_top_mulAut_le_two_of_linTwo_sq hp2 ⟨q, hd, hqp, h2⟩ ⟨e⟩) hAut
    · exact ⟨d, Or.inl ⟨q.exponent, h3, q, hd, hqp, rfl⟩, ⟨e⟩⟩
  · have hqp : q.p = p := by simpa [hd] using hpc.symm
    have hfe : d.1.fieldExponent = q.exponent := by simp [hd]
    rcases (show q.exponent = 1 ∨ 2 ≤ q.exponent by have := q.exponent_pos; omega) with h1 | h2
    · exact absurd (pRank_top_mulAut_le_two_of_unitary_one ⟨q, hqp, hd⟩ (hfe.trans h1) ⟨e⟩) hAut
    · exact ⟨d, Or.inr (Or.inl ⟨⟨q, hqp, hd⟩, hfe ▸ h2⟩), ⟨e⟩⟩
  · exact ⟨d, Or.inr (Or.inr ⟨by simpa [hd] using hpc, m, hd⟩), ⟨e⟩⟩

end CFSG.AGLEmbedding
