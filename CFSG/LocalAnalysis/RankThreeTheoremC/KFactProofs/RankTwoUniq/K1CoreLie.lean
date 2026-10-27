module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreU3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreL34
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq.K1CoreL28
public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactSeitzRankThree
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2SporRows3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

section Lie


variable {X : Type} [Group X] [Finite X]

theorem k1Core_eq_bot_of_lie {R : Sylow 3 X} {A X₀ K B W : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hBR : B ≤ R) (hB : IsElemAbelian 3 B)
    (hBc : Nat.card B = 9) (hconj : ∀ g : X, B.map (MulAut.conj g).toMonoidHom ≠ A)
    (hRA : (R : Subgroup X) ≠ A) (hAW : A ≤ Subgroup.normalizer (W : Set X))
    (hWc : Nat.Coprime (Nat.card W) 6) : W = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hc : 3 = d.1.characteristic
  · exfalso
    by_cases hsmall : IsD2LieCharSmall 3 d.1
    · have hRK := h.sylow_le_of_not_dvd_card_outer
        (kFactLieCharOut K d ⟨e⟩ 3 Nat.prime_three (by norm_num) hsmall)
      obtain ⟨q, hqp, hq⟩ := hsmall
      rcases hq with ⟨hq2, hd⟩ | ⟨hq1, hd | hd⟩
      · rcases (show q.exponent = 1 ∨ q.exponent = 2 by have := q.exponent_pos; omega) with
          h1 | h2
        ·
          have := kFactLinTwoPrimeRank K d ⟨e⟩ 3 Nat.prime_three (by norm_num) ⟨q, hqp, h1, hd⟩
          have := h.two_le_pRank_of_sylow_le hRK
          omega
        ·
          obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 3) (n := 2) (d := d)
            ⟨q, hd, hqp, h2⟩
          exact hRA (h.sylow_inf_eq_of_psl2 (e.trans e')).2
      ·
        refine h.not_le (h.le_of_glbCore_eq_top (R.subtype hRK).isPGroup' ?_
          (kFactLinThreeCore K d ⟨e⟩ 3 Nat.prime_three (by norm_num) ⟨q, hqp, hq1, hd⟩
            (R.subtype hRK)))
        rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hRK]
      ·
        exact k1Core_false_of_u3 h e ⟨q, hqp, hq1, hd⟩ hBR hB hBc hconj
    · exact h.false_of_three_le_pRank
        (kFactLieCharRank K d ⟨e⟩ 3 Nat.prime_three (by norm_num) hc hsmall)
  · by_cases hex : IsD2SeitzException 3 d.1
    · rcases hex with ⟨-, hex⟩ | ⟨h35, -⟩
      · rcases hex with ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq2', hd⟩ | ⟨q, hq2, hq1, hd⟩ |
          ⟨q, hq2, hq1, hd⟩ | hd
        ·
          have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨e'⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex (p := 2) (n := 3) (d := d)
            ⟨q, hd, hq2, hq3⟩
          exact k1Core_eq_bot_of_l28 h (e.trans e') hAW hWc
        ·
          exact k1Core_eq_bot_of_l34 h ⟨q, hq2, hq2', hd⟩ e hAW hWc
        ·
          exact (h.false_of_three_le_pRank
            (kFactSeitzRankThreeExceptions K d ⟨q, hq2, hq1, Or.inl hd⟩ ⟨e⟩)).elim
        ·
          exact (h.false_of_three_le_pRank
            (kFactSeitzRankThreeExceptions K d ⟨q, hq2, hq1, Or.inr hd⟩ ⟨e⟩)).elim
        ·
          exact (d2VacuousAt_tits_three d hd X R A X₀ K h ⟨e⟩).elim
      · norm_num at h35
    · exact (h.false_of_seitz CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds d e hc
        hex).elim

end Lie

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
