module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

variable {X : Type} [Group X] [Finite X]

theorem exists_rank_two_of_bad_aux_pull {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hg : GNGood T T₁ T₂) (hL : LiftOf T L Ls)
    (hsl : gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : 1 < CFSG.Open.pRank r (gnA T T₁ Ls) ∨ 1 < CFSG.Open.pRank r (gnA T T₂ Ls)) :
    ∃ (Ti : Subgroup X) (r : ℕ), (Ti = T₁ ∨ Ti = T₂) ∧ r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set X) ⊓ L) := by
  rcases h with h | h
  · refine ⟨T₁, r, Or.inl rfl, hr, hr2, ?_⟩
    exact two_le_pRank_of_map (toStar T) hr hr2 _
      (le_trans h (CFSG.SectionRank.pRank_mono hr.one_lt (gnA_le_map_normalizer_one hg hL)))
  · refine ⟨T₂, r, Or.inr rfl, hr, hr2, ?_⟩
    exact two_le_pRank_of_map (toStar T) hr hr2 _
      (le_trans h (CFSG.SectionRank.pRank_mono hr.one_lt hsl))

theorem exists_rank_two_of_bad_aux_pow {Q : TauCeti.PrimePower} (hQ : Q.p = 2) :
    2 ∣ Q.card ∧ (Q.card ≠ 2 → 3 ≤ Q.card) := by
  have he := Q.exponent_pos
  have hc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  refine ⟨hc ▸ dvd_pow_self 2 he.ne', fun hne => ?_⟩
  by_contra hlt
  have h1 : 2 ≤ Q.card := by
    rw [hc]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) he
  omega

theorem exists_rank_two_of_bad_aux_even {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (he : Even Q.exponent) : 3 ≤ Q.card := by
  obtain ⟨k, hk⟩ := he
  have hpos := Q.exponent_pos
  have h2 : 2 ≤ Q.exponent := by omega
  have h4 : 2 ^ 2 ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) h2
  rw [TauCeti.PrimePower.card_def, hQ]
  norm_num at h4
  omega

theorem exists_rank_two_of_bad_aux_card {d : TauCeti.ValidLieTypeIndex} (hdr : IsRankTwoPlus d.1)
    (h : RankOneList d.1 ∨ RankTwoList d.1) :
    (3 ≤ indexQ d.1 ∧ 2 ∣ indexQ d.1) ∨ ∃ Q : TauCeti.PrimePower, d.1 = .A 4 Q ∧ Q.card = 2 := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨hrange, hdup⟩ := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hrange' := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange
  have hdup' := fun h => hdup ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 h)
  cases d1 with
  | A l Q =>
    have hQ : Q.p = 2 := hdr.1
    obtain ⟨hev, hge⟩ := exists_rank_two_of_bad_aux_pow hQ
    rcases l with _ | _ | _ | _ | _ | l
    · exact absurd hdr.2 (by norm_num)
    · exact absurd hdr.2 (by norm_num)
    · exact Or.inl ⟨hge fun hc => hdup' (Or.inr (Or.inl ⟨rfl, hc⟩)), hev⟩
    · exact Or.inl ⟨hge fun hc => hdup' (Or.inr (Or.inr ⟨rfl, hc⟩)), hev⟩
    · by_cases hc : Q.card = 2
      · exact Or.inr ⟨Q, rfl, hc⟩
      · exact Or.inl ⟨hge hc, hev⟩
    · exfalso
      simp [RankOneList, RankTwoList] at h
  | twistedA l Q =>
    have hQ : Q.p = 2 := hdr.1
    obtain ⟨hev, -⟩ := exists_rank_two_of_bad_aux_pow hQ
    rcases l with _ | _ | _ | _ | _ | l
    · exact absurd hdr.2 (by norm_num)
    · exact absurd hdr.2 (by norm_num)
    · exact absurd hdr.2 (by norm_num)
    · rcases h with h | h
      · exact h.elim
      · exact Or.inl ⟨exists_rank_two_of_bad_aux_even hQ h, hev⟩
    · rcases h with h | h
      · exact h.elim
      · exact Or.inl ⟨exists_rank_two_of_bad_aux_even hQ h, hev⟩
    · exfalso
      simp [RankOneList, RankTwoList] at h
  | B l Q =>
    have hQ : Q.p = 2 := hdr.1
    obtain ⟨hev, hge⟩ := exists_rank_two_of_bad_aux_pow hQ
    rcases l with _ | _ | _ | l
    · exact absurd hdr.2 (by norm_num)
    · exact absurd hdr.2 (by norm_num)
    · exact Or.inl ⟨hge fun hc => hrange'.2 ⟨rfl, hc⟩, hev⟩
    · exfalso
      simp [RankOneList, RankTwoList] at h
  | D l Q => exfalso; simp [RankOneList, RankTwoList] at h
  | twistedD l Q => exfalso; simp [RankOneList, RankTwoList] at h
  | G2 Q =>
    obtain ⟨hev, -⟩ := exists_rank_two_of_bad_aux_pow (hdr : Q.p = 2)
    exact Or.inl ⟨hrange', hev⟩
  | C _ _ => exact hdr.elim
  | E6 _ => exact hdr.elim
  | E7 _ => exact hdr.elim
  | E8 _ => exact hdr.elim
  | F4 _ => exact hdr.elim
  | twistedE6 _ => exact hdr.elim
  | trialityD4 _ => exact hdr.elim
  | suzuki _ => exact hdr.elim
  | reeG2 _ => exact hdr.elim
  | reeF4 _ => exact hdr.elim
  | tits => exact hdr.elim

theorem exists_rank_two_of_bad_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hLn : L.Normal)
    (h20 : CFSG.Open.pRank 3 L < 3)
    (hsl : gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T))
    (hbad : ¬ Small1522 ↥Ls) :
    ∃ (Ti : Subgroup X) (r : ℕ), (Ti = T₁ ∨ Ti = T₂) ∧ r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set X) ⊓ L) := by
  have hLs : CFSG.Open.IsComponentOf Ls ⊤ := hl.comp.1
  have hLsq : CFSG.Open.IsQuasisimple ↥Ls := hLs.2.2
  have hLsn : Ls.Normal := by
    rw [← hl.lift.2]
    exact Subgroup.Normal.map hLn (toStar T) (QuotientGroup.mk'_surjective _)
  have hinv := gnImg_le_normalizer_of_normal hLsn
  obtain ⟨-, -, hoddZ⟩ := centre_of_lift hl.gn hLs hl.lift
  have hpull : ∀ {r : ℕ}, r.Prime → r ≠ 2 →
      (1 < CFSG.Open.pRank r (gnA T T₁ Ls) ∨ 1 < CFSG.Open.pRank r (gnA T T₂ Ls)) →
      ∃ (Ti : Subgroup X) (r : ℕ), (Ti = T₁ ∨ Ti = T₂) ∧ r.Prime ∧ r ≠ 2 ∧
        2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set X) ⊓ L) :=
    fun hr hr2 h => exists_rank_two_of_bad_aux_pull hl.good hl.lift hsl hr hr2 h
  rcases rankDatum hT hl.gn hl.good.shape hl.comp hl.lift with
    ⟨d, hdr, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨⟨d, q, hq7, hd, ⟨e⟩⟩, hr⟩ |
      ⟨⟨d, q, hq3, hd, ⟨e⟩⟩, hr⟩
  ·
    have hm : mRankChev d.1 3 (Nat.card (Subgroup.center ↥(barO2 L))) < 3 := by
      rw [← hr 3 Nat.prime_three (by norm_num)]
      exact h20
    have hlist : RankOneList d.1 ∨ RankTwoList d.1 := by
      obtain ⟨-, -, h3, h4⟩ := mRank3_cases hdr (Nat.card (Subgroup.center ↥(barO2 L)))
      rcases h4 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · have := h3.2 h
        omega
      · omega
    rcases exists_rank_two_of_bad_aux_card hdr hlist with ⟨h3, h2⟩ | ⟨Q, hQ, hQc⟩
    · have hne1 : indexQ d.1 - 1 ≠ 1 := by omega
      have hqp : (indexQ d.1 - 1).minFac.Prime := Nat.minFac_prime hne1
      have hqd : (indexQ d.1 - 1).minFac ∣ indexQ d.1 - 1 := Nat.minFac_dvd _
      have hq2 : (indexQ d.1 - 1).minFac ≠ 2 := by
        intro h
        rw [h] at hqd
        omega
      exact hpull hqp hq2
        (k517_4b X T T₁ T₂ hl.gn hl.good Ls hl.comp hinv d hdr ⟨e⟩ _ hqp hqd)
    · exfalso
      apply hbad
      have hin : In1512 d.1 := by
        rw [hQ]
        exact hQc
      have hh2 : ∀ Q', d.1 ≠ .A 2 Q' := fun Q' h => by
        rw [hQ] at h
        cases h
      have hh4 : ∀ Q', d.1 ≠ .twistedA 4 Q' := fun Q' h => by
        rw [hQ] at h
        cases h
      have hQp : Q.p = 2 := by
        have := hdr
        rw [hQ] at this
        exact this.1
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hLsq hoddZ hin hh2 hh4 ⟨e⟩ hQp hQ hQc))))
  ·
    rcases hn with rfl | rfl
    · rcases (Nat.dvd_prime Nat.prime_three).1
          ((hKSMAlt ↥Ls hLsq 6 ⟨e⟩ hoddZ).1 (Or.inl rfl)) with h1 | h3
      · exfalso
        exact hbad (Or.inr (Or.inl (equiv_of_centre_bot (Subgroup.eq_bot_of_card_eq _ h1) e)))
      · exact hpull Nat.prime_three (by norm_num)
          (hl.good.centre Ls hl.comp hinv 3 Nat.prime_three (dvd_of_eq h3.symm))
    · exfalso
      exact hbad (Or.inr (Or.inr (Or.inl (equiv_of_centre_bot (Subgroup.eq_bot_of_card_eq _
        ((hKSMAlt ↥Ls hLsq 8 ⟨e⟩ hoddZ).2 le_rfl)) e))))
  ·
    rcases hn with rfl | ⟨h8, -⟩
    · exact hpull Nat.prime_three (by norm_num) (hl.good.alt7 Ls hLs hinv ⟨e⟩)
    · exfalso
      have h := hr 3 Nat.prime_three (by norm_num)
      omega
  ·
    exfalso
    have h1 : Nat.card (Subgroup.center ↥Ls) = 1 :=
      (hKSML3 ↥Ls hLsq d ⟨e⟩ hoddZ).1 (Or.inr ⟨q, hq7, hd⟩)
    obtain ⟨e'⟩ := equiv_of_centre_bot (Subgroup.eq_bot_of_card_eq _ h1) e
    exact hbad (Or.inl (Or.inl ⟨rfl, d, q, hq7, hd, ⟨e'⟩⟩))
  ·
    exfalso
    have h1 : Nat.card (Subgroup.center ↥Ls) = 1 :=
      hKSMOdd.2 ↥Ls hLsq d ⟨q, hq3, hd⟩ ⟨e⟩ hoddZ
    obtain ⟨e'⟩ := equiv_of_centre_bot (Subgroup.eq_bot_of_card_eq _ h1) e
    exact hbad (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, ⟨q, hq3, hd⟩, ⟨e'⟩⟩))))

theorem exists_rank_two_of_bad (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3) (k517_4b : K517_4b) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hLn : L.Normal)
    (h20 : CFSG.Open.pRank 3 L < 3)
    (hsl : gnA T T₂ Ls ≤ (Subgroup.normalizer (T₂ : Set X) ⊓ L).map (toStar T))
    (hbad : ¬ Small1522 ↥Ls) :
    ∃ (Ti : Subgroup X) (r : ℕ), (Ti = T₁ ∨ Ti = T₂) ∧ r.Prime ∧ r ≠ 2 ∧
      2 ≤ CFSG.Open.pRank r (Subgroup.normalizer (Ti : Set X) ⊓ L) :=
  exists_rank_two_of_bad_gen hT hKSMAlt hKSMOdd hKSMU4 hKSML3 k517_4b hl.toGen hLn h20 hsl
    hbad

end CFSG.LocalAnalysis.RankThreeUC.S15
