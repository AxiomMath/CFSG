module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.lieChar_cases (hrank : KFactLieCharRank) (hL3 : KFactLinThreeCore)
    (h : D2AlmostSimple p X R A X₀ K) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hp : p = d.1.characteristic) :
    ∃ q : TauCeti.PrimePower, q.p = p ∧
      ((q.exponent = 2 ∧ d.1 = .A 1 q) ∨ (q.exponent = 1 ∧ d.1 = .twistedA 2 q)) := by
  by_cases hsmall : IsD2LieCharSmall p d.1
  · have hRK := h.sylow_le_of_not_dvd_card_outer
      (kFactLieCharOut K d ⟨e⟩ p h.prime h.ne_two hsmall)
    obtain ⟨q, hqp, hq⟩ := hsmall
    rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
    · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with h1 | h2
      · have := kFactLinTwoPrimeRank K d ⟨e⟩ p h.prime h.ne_two ⟨q, hqp, h1, hd⟩
        have := h.two_le_pRank_of_sylow_le hRK
        omega
      · exact ⟨q, hqp, Or.inl ⟨h2, hd⟩⟩
    · exfalso
      refine h.not_le (h.le_of_glbCore_eq_top (R.subtype hRK).isPGroup' ?_
        (hL3 K d ⟨e⟩ p h.prime h.ne_two ⟨q, hqp, hq1, hd⟩ (R.subtype hRK)))
      rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRK]
    · exact ⟨q, hqp, Or.inr ⟨hq1, hd⟩⟩
  · exact (h.false_of_three_le_pRank (hrank K d ⟨e⟩ p h.prime h.ne_two hp hsmall)).elim

end CFSG.AGLEmbeddingD2
