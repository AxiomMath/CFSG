module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem case_table_1521_aux_equiv {S S' : Type} [Group S] [Group S'] (hZ : Subgroup.center S = ⊥)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* S')) : Nonempty (S ≃* S') := by
  obtain ⟨e⟩ := e
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem case_table_1521_aux_shape (d1 : TauCeti.LieTypeIndex) (hdr : IsRankTwoPlus d1)
    (hin : In1512 d1) (h : RankOneList d1 ∨ RankTwoList d1) :
    (∃ Q : TauCeti.PrimePower, Q.p = 2 ∧ d1 = .A 2 Q) ∨
      (RankTwoList d1 ∧
        ((∃ Q : TauCeti.PrimePower, Q.p = 2 ∧
          (d1 = .G2 Q ∨ d1 = .B 2 Q ∨ d1 = .A 3 Q ∨ d1 = .twistedA 3 Q)) ∨
        (∃ Q : TauCeti.PrimePower, Q.card = 2 ∧ d1 = .A 4 Q) ∨
        (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d1 = .twistedA 4 Q))) := by
  cases d1 with
  | A l Q =>
    obtain ⟨hQ, hl⟩ := hdr
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · omega
    · omega
    · exact Or.inl ⟨Q, hQ, rfl⟩
    · exact Or.inr ⟨h.resolve_left (fun h' => h'.elim),
        Or.inl ⟨Q, hQ, Or.inr (Or.inr (Or.inl rfl))⟩⟩
    · exact Or.inr ⟨h.resolve_left (fun h' => h'.elim), Or.inr (Or.inl ⟨Q, hin, rfl⟩)⟩
    · simp only [RankOneList, RankTwoList, or_self] at h
    · simp only [RankOneList, RankTwoList, or_self] at h
    · exact hin.elim
  | twistedA l Q =>
    obtain ⟨hQ, hl⟩ := hdr
    rcases l with _ | _ | _ | _ | _ | _ | l
    · omega
    · omega
    · omega
    · exact Or.inr ⟨h.resolve_left (fun h' => h'.elim),
        Or.inl ⟨Q, hQ, Or.inr (Or.inr (Or.inr rfl))⟩⟩
    · exact Or.inr ⟨h.resolve_left (fun h' => h'.elim), Or.inr (Or.inr ⟨Q, hin, rfl⟩)⟩
    · exact hin.elim
    · exact hin.elim
  | B l Q =>
    obtain ⟨hQ, hl⟩ := hdr
    rcases l with _ | _ | _ | _ | l
    · omega
    · omega
    · exact Or.inr ⟨trivial, Or.inl ⟨Q, hQ, Or.inr (Or.inl rfl)⟩⟩
    · simp only [RankOneList, RankTwoList, or_self] at h
    · exact hin.elim
  | D l Q => exact hin.elim
  | twistedD l Q =>
    obtain ⟨hQ, hl⟩ := hdr
    rcases l with _ | _ | _ | _ | _ | l
    · omega
    · omega
    · omega
    · omega
    · simp only [RankOneList, RankTwoList, or_self] at h
    · exact hin.elim
  | G2 Q => exact Or.inr ⟨trivial, Or.inl ⟨Q, hdr, Or.inl rfl⟩⟩
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

theorem case_table_1521_aux_centre (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (d : TauCeti.ValidLieTypeIndex) (hin : In1512 d.1)
    (hshape : (∃ Q : TauCeti.PrimePower, Q.p = 2 ∧
          (d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q ∨ d.1 = .twistedA 3 Q)) ∨
        (∃ Q : TauCeti.PrimePower, Q.card = 2 ∧ d.1 = .A 4 Q) ∨
        (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .twistedA 4 Q))
    (e : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h5 : mRankChev d.1 5 (Nat.card (Subgroup.center K)) ≤ 3) :
    Nat.card (Subgroup.center K) = 1 := by
  have hA2 : ∀ Q : TauCeti.PrimePower, d.1 ≠ .A 2 Q := by
    rcases hshape with ⟨Q', -, h | h | h | h⟩ | ⟨Q', -, h⟩ | ⟨Q', -, h⟩ <;>
      (intro Q h'; rw [h] at h'; cases h')
  by_cases hU4 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q
  · obtain ⟨Q, hQ⟩ := hU4
    have hQp : Q.p = 2 := by
      have := hin
      rw [hQ] at this
      exact this
    exact hKSMU4 K hK d ⟨Q, hQp, hQ⟩ e hodd
  · push Not at hU4
    have hk := hKSMOdd.1 K hK d hin hA2 hU4 e hodd
    by_cases hU5 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 4 Q
    · obtain ⟨Q, hQ⟩ := hU5
      have hQc : Q.card = 4 := by
        have := hin
        rw [hQ] at this
        exact this
      rw [hQ] at h5
      have h5' := not_dvd_of_rank_u5 hQc h5
      rcases (Nat.dvd_prime Nat.prime_five).1 (hk.1 ⟨Q, hQ⟩) with h | h
      · exact h
      · exact (h5' (by omega)).elim
    · push Not at hU5
      exact hk.2 hU5

theorem case_table_1521_aux_lie (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K)))
    (d : TauCeti.ValidLieTypeIndex) (hdr : IsRankTwoPlus d.1) (hin : In1512 d.1)
    (e : Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (h3 : mRankChev d.1 3 (Nat.card (Subgroup.center K)) < 3)
    (h5 : mRankChev d.1 5 (Nat.card (Subgroup.center K)) ≤ 3) :
    IsLThreeTwoPower (K ⧸ Subgroup.center K) ∨
      (IsK21dGroup K ∧ Subgroup.center K = ⊥ ∧
        2 ≤ mRankChev d.1 3 (Nat.card (Subgroup.center K))) := by
  obtain ⟨hc1, hc2, hc3, hc4⟩ := mRank3_cases hdr (Nat.card (Subgroup.center K))
  have hlist : RankOneList d.1 ∨ RankTwoList d.1 := by
    rcases hc4 with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have := hc3.2 h
      omega
    · omega
  rcases case_table_1521_aux_shape d.1 hdr hin hlist with ⟨Q, hQp, hQ⟩ | ⟨hr2, hshape⟩
  · exact Or.inl (Or.inr ⟨d, Q, hQp, hQ, e⟩)
  · have hZ1 := case_table_1521_aux_centre hKSMOdd hKSMU4 hK hodd d hin hshape e h5
    have hZ := Subgroup.card_eq_one.1 hZ1
    obtain ⟨e'⟩ := case_table_1521_aux_equiv hZ e
    refine Or.inr ⟨?_, hZ, (hc2.2 hr2).ge⟩
    rcases hshape with ⟨Q, hQp, hQ⟩ | ⟨Q, hQc, hQ⟩ | ⟨Q, hQc, hQ⟩
    · exact Or.inl ⟨d, Q, Or.inl ⟨hQp, hQ⟩, ⟨e'⟩⟩
    · exact Or.inr (Or.inl ⟨d, ⟨Q, hQc, hQ⟩, ⟨e'⟩⟩)
    · exact Or.inl ⟨d, Q, Or.inr ⟨hQc, hQ⟩, ⟨e'⟩⟩

theorem case_table_1521_aux_normal_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L) (hn : L.Normal)
    (h20 : CFSG.Open.pRank 3 L < 3) : Case21 T L := by
  have hJL : Subgroup.normalClosure (L : Set X) = L := Subgroup.normalClosure_eq_self L
  have h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3 := hl.rank_L
  have hdat := rankDatum1512_of_ctx hT hl.gn hl.good.shape hl.comp hl.lift h3
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hl.gn hl.comp.1 hl.lift
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hl.lift.1.component.2.2
  have hoddK : Odd (Nat.card (Subgroup.center ↥(barO2 L))) := centre_barO2_odd hl.lift.1
  unfold Case21
  rw [hJL]
  rcases hdat with ⟨d, hdr, hin, ⟨e⟩, hr⟩ | ⟨n, hn68, ⟨e⟩, hr⟩ | ⟨n, hn710, ⟨e⟩, hr⟩ |
    ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩ | ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩
  · have hm3 := hr 3 Nat.prime_three (by norm_num)
    have hm5 := hr 5 Nat.prime_five (by norm_num)
    rcases case_table_1521_aux_lie hKSMOdd hKSMU4 hK hoddK d hdr hin ⟨eQ.trans e⟩
      (by rw [← hm3]; exact h20) (by rw [← hm5]; exact h3 5 Nat.prime_five (by norm_num))
      with h | ⟨hS, hZ, h2⟩
    · exact Or.inl ⟨hn, Or.inr (Or.inr h)⟩
    · exact Or.inr (Or.inr (Or.inr ⟨hn, hS, hZ, by rw [hm3]; exact h2⟩))
  · rcases hn68 with rfl | rfl
    · exact Or.inl ⟨hn, Or.inl ⟨eQ.trans e⟩⟩
    · have hZ := Subgroup.card_eq_one.1
        ((hKSMAlt ↥(barO2 L) hK 8 ⟨eQ.trans e⟩ hoddK).2 (by norm_num))
      have hm3 := hr 3 Nat.prime_three (by norm_num)
      exact Or.inr (Or.inr (Or.inr ⟨hn, Or.inr (Or.inr (Or.inr ⟨8, Or.inr rfl,
        case_table_1521_aux_equiv hZ ⟨eQ.trans e⟩⟩)), hZ, by omega⟩))
  · have hm3 := hr 3 Nat.prime_three (by norm_num)
    rcases hn710 with rfl | rfl
    · have hg : gnImg T L = Ls := hl.lift.2
      exact Or.inr (Or.inr (Or.inl (Or.inl ⟨(MulEquiv.subgroupCongr hg).trans e⟩)))
    · omega
  · exact Or.inl ⟨hn, Or.inr (Or.inl ⟨d, ⟨q, hq, hd⟩, ⟨eQ.trans e⟩⟩)⟩
  · have hZ := Subgroup.card_eq_one.1
      (hKSMOdd.2 ↥(barO2 L) hK d ⟨q, hq, hd⟩ ⟨eQ.trans e⟩ hoddK)
    have hm3 := hr 3 Nat.prime_three (by norm_num)
    simp only [if_true] at hm3
    exact Or.inr (Or.inr (Or.inr ⟨hn, Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hq, hd⟩,
      case_table_1521_aux_equiv hZ ⟨eQ.trans e⟩⟩)), hZ, by omega⟩))

theorem case_table_1521_aux_normal (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hn : L.Normal)
    (h20 : CFSG.Open.pRank 3 L < 3) : Case21 T L :=
  case_table_1521_aux_normal_gen hT hKSMAlt hKSMOdd hKSMU4 hl.toGen hn h20

theorem case_table_1521_aux_gen (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hProd : L ≠ Subgroup.normalClosure (L : Set X) → IsLThreeOfExp 1 ↥(barO2 L) →
      Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3 →
        IsLThreeTwoProd 2 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) ∨
          IsLThreeTwoProd 3 ↥(gnImg T (Subgroup.normalClosure (L : Set X))))
    (h15 : Shape1515 L) (h20 : CFSG.Open.pRank 3 L < 3) : Case21 T L := by
  by_cases hJ : L = Subgroup.normalClosure (L : Set X)
  · haveI : L.Normal := by
      have h := (Subgroup.normalClosure_normal (s := (L : Set X)))
      rw [← hJ] at h
      exact h
    exact case_table_1521_aux_normal_gen hT hKSMAlt hKSMOdd hKSMU4 hl this h20
  · unfold Case21
    rcases h15 with hJ' | hcp | ⟨hL3, hk⟩
    · exact (hJ hJ').elim
    · exact Or.inr (Or.inl hcp)
    · exact Or.inr (Or.inr (Or.inl (Or.inr (hProd hJ hL3 hk))))

theorem case_table_1521_aux (hT : LieOddRankTable) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd)
    (hKSMU4 : KSMU4) (hKSML3 : KSML3)
    (hProd : ∀ (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
      {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (hne : L ≠ Subgroup.normalClosure (L : Set X))
      (hL3 : IsLThreeOfExp 1 ↥(barO2 L))
      (hk : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3),
      IsLThreeTwoProd 2 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) ∨
        IsLThreeTwoProd 3 ↥(gnImg T (Subgroup.normalClosure (L : Set X)))) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hl : LiftCtx X T T₁ T₂ Ls L) (h15 : Shape1515 L)
    (h20 : CFSG.Open.pRank 3 L < 3) : Case21 T L :=
  case_table_1521_aux_gen hT hKSMAlt hKSMOdd hKSMU4 hl.toGen
    (fun hne hL3 hk => hProd hKSML3 hl hne hL3 hk) h15 h20

end CFSG.LocalAnalysis.RankThreeUC.S15
