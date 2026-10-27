module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourSolvThreeTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding

@[expose] def ThreeFourSolvThreeLTwoTwentySeven : Prop :=
  ∀ (q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), q.p = 3 → q.exponent = 3 →
    d.1 = .A 1 q → ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group

theorem threeFourSolvThreeNoneAt_linTwo_of_four_le (q : TauCeti.PrimePower)
    (d : TauCeti.ValidLieTypeIndex) (hq3 : q.p = 3) (hq4 : 4 ≤ q.exponent) (hd : d.1 = .A 1 q) :
    ThreeFourSolvThreeNoneAt (TauCeti.CFSGIndex.lie d).Group := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdL : IsLinTwoIndex 3 q.exponent d := ⟨q, hd, hq3, rfl⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hdL
  refine ThreeFourSolvThreeNoneAt.of_mulEquiv e.symm (ThreeFourSolvThreeNoneAt.of_lt_pRank ?_)
  obtain ⟨T⟩ : Nonempty (Sylow 3 (PSL2GF 3 q.exponent)) := inferInstance
  obtain ⟨hel, hcard⟩ := psl2GF_sylow 3 q.exponent (by omega) T
  have h1 : q.exponent ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (PSL2GF 3 q.exponent)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hel hcard
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  omega

theorem threeFourSolvThreeLinTwo_of (h27 : ThreeFourSolvThreeLTwoTwentySeven) :
    ThreeFourSolvThreeLinTwo := by
  intro q d hq3 hq2 hd
  rcases Nat.lt_or_ge q.exponent 4 with h4 | h4
  · interval_cases hqe : q.exponent
    ·
      exfalso
      have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).2
      rw [hd, TauCeti.LieTypeIndex.isDuplicateRepresentative_iff] at hv
      have hcard : q.card = 9 := by rw [TauCeti.PrimePower.card_def, hq3, hqe]; norm_num
      exact hv (Or.inl ⟨rfl, Or.inr (Or.inr hcard)⟩)
    · exact h27 q d hq3 hqe hd
  · exact threeFourSolvThreeNoneAt_linTwo_of_four_le q d hq3 h4 hd

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
