module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeOneReductions
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieCharPAll

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section LieCharCert


variable {p : ℕ} {G : Type} [Group G] [Finite G] {K : Subgroup G} {P : Sylow p G}
  {E : Subgroup G}

theorem Hyp.threeOne_lieChar (H : Hyp p K P E) (h3 : 3 ≤ Open.pRank p (P : Subgroup G))
    (hnot : ¬ K ≤ GLBWeakCore p (P : Subgroup G)) (hC : Subgroup.centralizer (K : Set G) = ⊥)
    (d : TauCeti.ValidLieTypeIndex) (hpd : p = d.1.characteristic)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) : OnThreeOneList p K := by
  by_cases hrank : IsRankOneLieIndex d.1
  · rcases hrank with ⟨q, hd⟩ | ⟨q, hd⟩ | ⟨m, hd⟩
    · have hqp : q.p = p := by
        rw [hd] at hpd
        simpa using hpd.symm
      by_cases h1 : q.exponent = 1
      · have hPK : (P : Subgroup G) ≤ K := H.le_of_not_dvd_card_outer hC
          (CFSG.AGLEmbeddingD2.kFactLieCharOut K d ⟨e⟩ p H.prime H.ne_two
            ⟨q, hqp, Or.inl ⟨by omega, hd⟩⟩)
        have hr := CFSG.AGLEmbeddingD2.kFactLinTwoPrimeRank K d ⟨e⟩ p H.prime H.ne_two
          ⟨q, hqp, h1, hd⟩
        have := H.pRank_le_of_le hPK
        omega
      · have := q.exponent_pos
        exact ⟨.lie d, Or.inl (Or.inl ⟨q, hqp, by omega, hd⟩), ⟨e⟩⟩
    · have hqp : q.p = p := by
        rw [hd] at hpd
        simpa using hpd.symm
      exact ⟨.lie d, Or.inl (Or.inr (Or.inl ⟨q, hqp, hd⟩)), ⟨e⟩⟩
    · have hp3 : p = 3 := by
        rw [hd] at hpd
        simpa using hpd
      exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, m, hd⟩))))), ⟨e⟩⟩
  by_cases hB2 : IsSpFourIndex p d
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inl hB2))), ⟨e⟩⟩
  by_cases hL3 : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q
  · exact ⟨.lie d, Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hL3)))), ⟨e⟩⟩
  obtain ⟨hs, hnab, -⟩ := H.isCatalogGroup (H.center_eq_bot_of_centralizer_eq_bot hC)
  exact (hnot (H.le_weakCore_of_sylow fun T =>
    weakCharPGenAt_or weakCharPGenAt_sl (weakCharPGenAt_or weakCharPGenAt_sp
      (weakCharPGenAt_or weakCharPGenAt_su (weakCharPGenAt_or weakCharPGenAt_bOdd
        (weakCharPGenAt_or weakCharPGenAt_d (weakCharPGenAt_or weakCharPGenAt_twistedD
          weakCharPGenAt_exceptional))))) K hs hnab d
      (exists_weak_family_of_odd H.ne_two hpd hrank hB2 hL3) ⟨e⟩ p H.prime H.ne_two hpd hrank
      T)).elim

end LieCharCert

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.ThreeOne
