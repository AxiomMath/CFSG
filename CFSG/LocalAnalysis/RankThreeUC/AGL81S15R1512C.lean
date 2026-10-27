module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512A

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open KFactsPair
open scoped commutatorElement

section Row12

variable {X : Type} [Group X] [Finite X]

theorem equiv_of_centre_bot {S G' : Type*} [Group S] [Group G'] (h : Subgroup.center S = ⊥)
    (e : (S ⧸ Subgroup.center S) ≃* G') : Nonempty (S ≃* G') :=
  ⟨(QuotientGroup.quotientBot (G := S)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h.symm).trans e)⟩

theorem centre_eq_bot_of_in1512 (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.IsQuasisimple S) {d : TauCeti.ValidLieTypeIndex} (hd : In1512 d.1)
    (h2 : ∀ Q, d.1 ≠ .A 2 Q) (h4 : ∀ Q, d.1 ≠ .twistedA 4 Q)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hodd : Odd (Nat.card (Subgroup.center S))) : Subgroup.center S = ⊥ := by
  by_cases h3 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q
  · obtain ⟨Q, hQ⟩ := h3
    have hQ2 : Q.p = 2 := by
      have := hd
      rw [hQ] at this
      exact this
    exact Subgroup.eq_bot_of_card_eq _ (hKSMU4 S hS d ⟨Q, hQ2, hQ⟩ e hodd)
  · push Not at h3
    exact Subgroup.eq_bot_of_card_eq _ ((hKSMOdd.1 S hS d hd h2 h3 e hodd).2 h4)

theorem centre_eq_bot_of_u5 (hKSMOdd : KSMOdd) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.IsQuasisimple S) {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hc : Q.card = 4) (hd : d.1 = .twistedA 4 Q)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hodd : Odd (Nat.card (Subgroup.center S))) (h5 : ¬ 5 ∣ Nat.card (Subgroup.center S)) :
    Subgroup.center S = ⊥ := by
  have hin : In1512 d.1 := by rw [hd]; exact hc
  have h2 : ∀ Q', d.1 ≠ .A 2 Q' := fun Q' h => by rw [hd] at h; cases h
  have h3 : ∀ Q', d.1 ≠ .twistedA 3 Q' := fun Q' h => by rw [hd] at h; cases h
  have hdvd := (hKSMOdd.1 S hS d hin h2 h3 e hodd).1 ⟨Q, hd⟩
  apply Subgroup.eq_bot_of_card_eq
  rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
  · exact h
  · exact absurd (h ▸ dvd_refl _) h5

theorem isLThreeOfExp_of_A2 {S : Type} [Group S] {d : TauCeti.ValidLieTypeIndex}
    {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hd : d.1 = .A 2 Q)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : IsLThreeOfExp Q.exponent S := by
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  right
  have h2 : 2 ≤ Q.exponent := by
    have hexp := Q.exponent_pos
    by_contra hlt
    have h1 : Q.exponent = 1 := by omega
    refine ((TauCeti.LieTypeIndex.valid_iff _).1 hv).2
      ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inl ⟨rfl, ?_⟩)))
    rw [TauCeti.PrimePower.card_def, hQ, h1]
    norm_num
  exact ⟨h2, ⟨_, hv⟩, Q, hQ, rfl, rfl, ⟨e⟩⟩

theorem one_lt_mN_of_minOverBorel {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls)) {P : Subgroup (X ⧸ gnC T)}
    (hP : IsMinOverBorel Ls (gnImg T T ⊓ Ls) P) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h2 : 2 ≤ CFSG.Open.pRank q (pElementSubgroup 2 P)) : 1 < mN T₁ q ∨ 1 < mN T₂ q := by
  have hO : pElementSubgroup 2 P ≤ Ls := (pElementSubgroup_le P).trans hP.1
  rcases hg.parabolic Ls hLs hchev P hP with h | h
  · left
    have hA : pElementSubgroup 2 P ≤ gnA T T₁ Ls :=
      le_inf (h.trans (Subgroup.map_mono (Subgroup.centralizer_le_normalizer _))) hO
    have h2' : 1 < CFSG.Open.pRank q (gnA T T₁ Ls) :=
      lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hq.one_lt hA))
    exact two_le_pRank_normalizer_of_gnA T T₁ Ls hq hq2 h2'
  · right
    have hA : pElementSubgroup 2 P ≤ gnA T T₂ Ls := le_inf h hO
    have h2' : 1 < CFSG.Open.pRank q (gnA T T₂ Ls) :=
      lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hq.one_lt hA))
    exact two_le_pRank_normalizer_of_gnA T T₂ Ls hq hq2 h2'

theorem two_le_mN_of_u5 (hKParU5 : KParU5) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hc : Q.card = 4)
    (hd : d.1 = .twistedA 4 Q)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    1 < mN T₁ 5 ∨ 1 < mN T₂ 5 := by
  obtain ⟨P, hP, hrk⟩ := hKParU5 X T hX Ls hLs d Q hQ hd e
  have hchev : IsChevTwo (↥Ls ⧸ Subgroup.center ↥Ls) := by
    obtain ⟨e'⟩ := e
    exact Or.inl ⟨d, by rw [hd]; exact hQ, ⟨e'⟩⟩
  have h5 : 2 ≤ CFSG.Open.pRank 5 (pElementSubgroup 2 P) :=
    hrk 5 Nat.prime_five (by rw [hc])
  exact one_lt_mN_of_minOverBorel hg hLs hchev hP Nat.prime_five (by norm_num) h5

theorem isSLThreeOver_of_K541 (hK541 : K541) {T : Subgroup X} (hX : GNSetting X T)
    {Ls : Subgroup (X ⧸ gnC T)} (hLs : IsComponentOf Ls ⊤)
    (hcomm : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls) {n : ℕ} (hn : 0 < n)
    (h : IsLThreeOfExp n (↥Ls ⧸ Subgroup.center ↥Ls)) : IsSLThreeOver (fun _ => True) ↥Ls :=
  ⟨n, hn, trivial, hK541 X T hX Ls hLs hcomm n h⟩

theorem isLieIdxOver_of_quotCenter (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) {S : Type} [Group S]
    [Finite S] (hS : CFSG.Open.IsQuasisimple S) (hodd : Odd (Nat.card (Subgroup.center S)))
    {d : TauCeti.ValidLieTypeIndex} (hd : In1512 d.1) (h2 : ∀ Q, d.1 ≠ .A 2 Q)
    (h4 : ∀ Q, d.1 ≠ .twistedA 4 Q)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group))
    {f : TauCeti.PrimePower → TauCeti.LieTypeIndex} {c : ℕ → Prop} {Q : TauCeti.PrimePower}
    (hQ : Q.p = 2) (hf : d.1 = f Q) (hc : c Q.card) : IsLieIdxOver S f c := by
  have hbot := centre_eq_bot_of_in1512 hKSMOdd hKSMU4 hS hd h2 h4 e hodd
  obtain ⟨e'⟩ := e
  exact ⟨Q, hQ, hc, d, hf, ⟨(QuotientGroup.quotientBot (G := S)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e')⟩⟩

theorem isGroupOf1512_of_lie_gen (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hK541 : K541)
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hshape : GNShape T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) {d : TauCeti.ValidLieTypeIndex} (hdr : IsRankTwoPlus d.1)
    (hd : In1512 d.1)
    (e : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hr : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r L = mRankChev d.1 r (Nat.card (Subgroup.center ↥(barO2 L))))
    (h5 : ∀ Q : TauCeti.PrimePower, Q.p = 2 → Q.card = 4 → d.1 = .twistedA 4 Q →
      CFSG.Open.pRank 5 L ≤ 3) : IsGroupOf1512 ↥Ls := by
  obtain ⟨-, hdvdZ, hodd⟩ := centre_of_lift hX hLs.1 hL
  have hS : CFSG.Open.IsQuasisimple ↥Ls := hLs.1.2.2
  have hcomm := (hshape Ls hLs).1
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A l Q =>
    have hQ : Q.p = 2 := hdr.1
    rcases l with _ | _ | _ | _ | _ | _ | _ | l
    · exact (hd : False).elim
    · exact (hd : False).elim
    · obtain ⟨e'⟩ := e
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isSLThreeOver_of_K541 hK541 hX hLs.1 hcomm
          Q.exponent_pos (isLThreeOfExp_of_A2 hQ rfl e'))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (isLieIdxOver_of_quotCenter
        hKSMOdd hKSMU4 hS hodd hd (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl (show Q.card = 2 from hd))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl (show Q.card = 2 from hd)))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl (show Q.card = 2 from hd))))))))))))))
    · exact (hd : False).elim
  | twistedA l Q =>
    have hQ : Q.p = 2 := hdr.1
    rcases l with _ | _ | _ | _ | _ | l
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (isLieIdxOver_of_quotCenter
        hKSMOdd hKSMU4 hS hodd hd (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial)))))))
    · have hc : Q.card = 4 := hd
      have h5m : mRankChev (.twistedA 4 Q) 5
          (Nat.card (Subgroup.center ↥(barO2 L))) ≤ 3 := by
        rw [← hr 5 Nat.prime_five (by norm_num)]
        exact h5 Q hQ hc rfl
      have h5' : ¬ 5 ∣ Nat.card (Subgroup.center ↥Ls) :=
        fun h => not_dvd_of_rank_u5 hc h5m (h.trans hdvdZ)
      have hbot := centre_eq_bot_of_u5 hKSMOdd hS hc rfl e hodd h5'
      obtain ⟨e'⟩ := e
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (⟨Q, hQ, hc, ⟨_, hv⟩, rfl, ⟨(QuotientGroup.quotientBot (G :=
          ↥Ls)).symm.trans ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e')⟩⟩)))))))))))))
    · exact (hd : False).elim
  | B l Q =>
    have hQ : Q.p = 2 := hdr.1
    rcases l with _ | _ | _ | _ | l
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl
        (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial)))))))))
    · exact (hd : False).elim
  | twistedD l Q =>
    have hQ : Q.p = 2 := hdr.1
    rcases l with _ | _ | _ | _ | _ | l
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact (hd : False).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS hodd hd
        (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial))))))))))
    · exact (hd : False).elim
  | G2 Q =>
    have hQ : Q.p = 2 := hdr
    exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (isLieIdxOver_of_quotCenter hKSMOdd hKSMU4 hS
        hodd hd (fun Q' h => by first | cases h | simp at h)
        (fun Q' h => by first | cases h | simp at h) e hQ rfl trivial)))))
  | C _ _ => exact (hd : False).elim
  | D _ _ => exact (hd : False).elim
  | E6 _ => exact (hd : False).elim
  | E7 _ => exact (hd : False).elim
  | E8 _ => exact (hd : False).elim
  | F4 _ => exact (hd : False).elim
  | twistedE6 _ => exact (hd : False).elim
  | trialityD4 _ => exact (hd : False).elim
  | suzuki _ => exact (hd : False).elim
  | reeG2 _ => exact (hd : False).elim
  | reeF4 _ => exact (hd : False).elim
  | tits => exact (hd : False).elim

theorem isGroupOf1512_of_alt (hKSMAlt : KSMAlt) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.IsQuasisimple S) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* alternatingGroup (Fin n)))
    (hodd : Odd (Nat.card (Subgroup.center S))) : IsGroupOf1512 S := by
  have hk := hKSMAlt S hS n e hodd
  obtain ⟨e'⟩ := e
  rcases hn with rfl | rfl
  · rcases (Nat.dvd_prime Nat.prime_three).1 (hk.1 (Or.inl rfl)) with h1 | h3
    · have hbot := Subgroup.eq_bot_of_card_eq _ h1
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
        ⟨trivial, ⟨(QuotientGroup.quotientBot (G := S)).symm.trans
          ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e')⟩⟩))))))))
    · exact Or.inl ⟨hS, h3, ⟨e'⟩⟩
  · have hbot := Subgroup.eq_bot_of_card_eq _ (hk.2 (le_refl 8))
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
      ⟨trivial, ⟨(QuotientGroup.quotientBot (G := S)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e')⟩⟩))))))

theorem isUThreeThree_of_quotCenter (hKSMOdd : KSMOdd) {S : Type} [Group S] [Finite S]
    (hS : CFSG.Open.IsQuasisimple S) {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Nonempty ((S ⧸ Subgroup.center S) ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hodd : Odd (Nat.card (Subgroup.center S))) : IsUThreeThree S := by
  have hc : Nat.card (Subgroup.center S) = 1 := hKSMOdd.2 S hS d ⟨q, hq, hd⟩ e hodd
  have hbot : Subgroup.center S = ⊥ := Subgroup.eq_bot_of_card_eq _ hc
  obtain ⟨e⟩ := e
  exact ⟨d, ⟨q, hq, hd⟩, ⟨(QuotientGroup.quotientBot (G := S)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hbot.symm).trans e)⟩⟩

theorem isGroupOf1512_of_datum_gen (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSMAlt : KSMAlt)
    (hK541 : K541)
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hshape : GNShape T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hdat : RankDatum1512 T L Ls)
    (h5 : ∀ (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Q.p = 2 →
      Q.card = 4 → d.1 = .twistedA 4 Q →
      Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      CFSG.Open.pRank 5 L ≤ 3) : IsGroupOf1512 ↥Ls := by
  obtain ⟨-, -, hodd⟩ := centre_of_lift hX hLs.1 hL
  have hcomm := (hshape Ls hLs).1
  rcases hdat with ⟨d, hdr, hd, e, hr⟩ | ⟨n, hn, e, -⟩ | ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨d, q, hq, hd, e⟩, -⟩ |
    ⟨⟨d, q, hq, hd, e⟩, -⟩
  · exact isGroupOf1512_of_lie_gen hKSMOdd hKSMU4 hK541 hX hshape hLs hL hdr hd e hr
      (fun Q hQ hc hdQ => h5 d Q hQ hc hdQ e)
  · exact isGroupOf1512_of_alt hKSMAlt hLs.1.2.2 hn e hodd
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isSLThreeOver_of_K541 hK541 hX hLs.1 hcomm Nat.one_pos
        (Or.inl ⟨rfl, d, q, hq, hd, e⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr
      ⟨trivial, isUThreeThree_of_quotCenter hKSMOdd hLs.1.2.2 hq hd e hodd⟩))))

theorem isGroupOf1512_of_datum (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4) (hKSMAlt : KSMAlt) (hK541 : K541)
    {T T₁ T₂ : Subgroup X} (hX : GNSetting X T) (hshape : GNShape T T₁ T₂)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hdat : RankDatum1512 T L Ls)
    (h3 : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 3) : IsGroupOf1512 ↥Ls :=
  isGroupOf1512_of_datum_gen hKSMOdd hKSMU4 hKSMAlt hK541 hX hshape hLs hL hdat
    (fun _ _ _ _ _ _ => h3 5 Nat.prime_five (by norm_num))

end Row12

end CFSG.LocalAnalysis.RankThreeUC.S15
