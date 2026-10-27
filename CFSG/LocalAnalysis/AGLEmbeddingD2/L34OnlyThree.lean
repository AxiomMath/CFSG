module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Three
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PrimeThree3Seitz
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeCore

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

theorem D2AlmostSimple.exists_l34_of_cases {X : Type} [Group X] [Finite X] {R : Sylow 3 X}
    {A X₀ K : Subgroup X} (hK : D2AlmostSimple 3 X R A X₀ K) (hrank : KFactLieCharRank)
    (hS : D2SeitzCross) (h3 : KFactSeitzRankThreeExceptions)
    (hA6 : ∀ hn : 5 ≤ 2 * 3,
      Nonempty (K ≃* (TauCeti.CFSGIndex.alternating (2 * 3) hn).Group) → False)
    (hThree : ∀ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q) →
      3 = d.1.characteristic → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → False)
    (hL28 : ∀ d : TauCeti.ValidLieTypeIndex,
      CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight 3 d.1 →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → False)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits →
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) → False)
    (hSpor : ∀ s : TauCeti.SporadicName,
      Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False) :
    ∃ d' : TauCeti.ValidLieTypeIndex, IsL34Index d' ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d').Group) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ := hK.catalog
  cases i with
  | cyclic q hq =>
    obtain ⟨e⟩ := hi
    exact (hK.false_of_cyclic q hq e).elim
  | alternating n hn =>
    obtain ⟨e⟩ := hi
    have hn6 : n = 2 * 3 := hK.eq_two_mul_of_alternating hn e
    subst hn6
    exact (hA6 hn ⟨e⟩).elim
  | sporadic s =>
    exact (hSpor s hi).elim
  | lie d =>
    obtain ⟨e⟩ := hi
    by_cases hchar : 3 = d.1.characteristic
    ·
      exfalso
      by_cases hsmall : IsD2LieCharSmall 3 d.1
      · have hRK := hK.sylow_le_of_not_dvd_card_outer
          (kFactLieCharOut K d ⟨e⟩ 3 hK.prime hK.ne_two hsmall)
        obtain ⟨q, hqp, hq⟩ := hsmall
        rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
        · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with
            h1 | h2
          · have := kFactLinTwoPrimeRank K d ⟨e⟩ 3 hK.prime hK.ne_two ⟨q, hqp, h1, hd⟩
            have := hK.two_le_pRank_of_sylow_le hRK
            omega
          · have := five_le_of_valid_A_one hd h2 (by rw [hqp]; norm_num)
            omega
        · refine hK.not_le (hK.le_of_glbCore_eq_top (R.subtype hRK).isPGroup' ?_
            (kFactLinThreeCore K d ⟨e⟩ 3 hK.prime hK.ne_two ⟨q, hqp, hq1, hd⟩
              (R.subtype hRK)))
          rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRK]
        · exact hThree d ⟨q, hq1, hd⟩ hchar ⟨e⟩
      · exact hK.false_of_three_le_pRank (hrank K d ⟨e⟩ 3 hK.prime hK.ne_two hchar hsmall)
    · by_cases hexcp : IsD2SeitzException 3 d.1
      · rcases hexcp with ⟨-, h3⟩ | ⟨h5, -⟩
        · rcases h3 with ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ |
            ⟨q, hq2, hq1, hd⟩ | hd
          · exact (hL28 d ⟨rfl, q, hq2, hq3, hd⟩ ⟨e⟩).elim
          · exact ⟨d, ⟨q, hq2, hq2', hd⟩, ⟨e⟩⟩
          · exact (hK.false_of_three_le_pRank
              (h3 K d ⟨q, hq2, hq1, Or.inl hd⟩ ⟨e⟩)).elim
          · exact (hK.false_of_three_le_pRank
              (h3 K d ⟨q, hq2, hq1, Or.inr hd⟩ ⟨e⟩)).elim
          · exact (hTits d hd ⟨e⟩).elim
        · omega
      · exact (hK.false_of_seitzCross hS d e hchar hexcp).elim

theorem d2OnlyL34Three_of (hrank : KFactLieCharRank) (hS : D2SeitzCross) (hA6 : D2AltSixCase)
    (hThree : D2U3Three)
    (hL28 : ∀ d : TauCeti.ValidLieTypeIndex,
      D2IndexCaseAt (.lie d) fun p => CFSG.LocalAnalysis.RankThreeTheoremC.IsD2SeitzLTwoEight p d.1)
    (hTits : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .tits → D2IndexCaseAt (.lie d) fun p => p = 3)
    (hSpor : ∀ s : TauCeti.SporadicName, D2IndexCaseAt (.sporadic s) fun p => p = 3) :
    D2OnlyL34Three := by
  intro G _ _ hglob hD1 hβ P M A H R hesc hmax Rbar K hRbar hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact hK.exists_l34_of_cases hrank hS kFactSeitzRankThreeExceptions
    (fun _ he => hA6 G hglob hD1 3 rfl P M A H R hesc hmax hβ Rbar K hRbar hK he)
    (fun d hd hchar he => hThree d hd G hglob hD1 3 ⟨hchar, rfl⟩ P M A H R hesc hmax hβ Rbar K
      hRbar hK he)
    (fun d hd he => hL28 d G hglob hD1 3 hd P M A H R hesc hmax hβ Rbar K hRbar hK he)
    (fun d hd he => hTits d hd G hglob hD1 3 rfl P M A H R hesc hmax hβ Rbar K hRbar hK he)
    fun s he => hSpor s G hglob hD1 3 rfl P M A H R hesc hmax hβ Rbar K hRbar hK he

end CFSG.AGLEmbeddingD2
