module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankCases
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankEq2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section TableLookups

variable {X : Type} [Group X] [Finite X]

theorem centre_barO2_eq_bot_of_A7 {L : Subgroup X}
    (h : Nonempty (↥(barO2 L) ≃* alternatingGroup (Fin 7))) :
    Nat.card (Subgroup.center ↥(barO2 L)) = 1 := by
  obtain ⟨e⟩ := h
  exact Subgroup.card_eq_one.2 (quotCenter_equiv_alt (by norm_num) e).1

theorem card_eq_two_pow_s15 {Q : TauCeti.PrimePower} (hQ : Q.p = 2) : Q.card = 2 ^ Q.exponent := by
  rw [← hQ]; exact (ksm_card_eq rfl).symm

theorem rankOneList_cases {i : TauCeti.LieTypeIndex} (h : RankOneList i) :
    ∃ Q : TauCeti.PrimePower, i = .A 2 Q ∧ Odd Q.exponent := by
  cases i with
  | A l Q =>
    rcases l with _ | _ | _ | l <;> simp [RankOneList] at h
    exact ⟨Q, rfl, h⟩
  | _ => simp [RankOneList] at h

theorem two_le_exponent_of_A2 {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower}
    (hQ : Q.p = 2) (hd : d.1 = .A 2 Q) : 2 ≤ Q.exponent := by
  have hv := (TauCeti.LieTypeIndex.valid_iff d.1).1 d.2
  rw [hd] at hv
  have hnd : ¬ (TauCeti.LieTypeIndex.A 2 Q).IsDuplicateRepresentative := hv.2
  have hc : Q.card ≠ 2 := fun h => hnd
    ((TauCeti.LieTypeIndex.isDuplicateRepresentative_iff _).2 (Or.inr (Or.inl ⟨rfl, h⟩)))
  have hexp : Q.card = 2 ^ Q.exponent := card_eq_two_pow_s15 hQ
  have hpos := Q.exponent_pos
  by_contra hlt
  have h1 : Q.exponent = 1 := by omega
  apply hc
  rw [hexp, h1]
  norm_num

theorem rankOneShape_of_datum (hKSML3 : KSML3) {T L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤) (hL : LiftOf T L Ls)
    (hdat : RankDatum1512 T L Ls) (h : CFSG.Open.pRank 3 L = 1) :
    Nat.card (Subgroup.center ↥(barO2 L)) = 1 ∧
      ((∃ (m : ℕ) (d : TauCeti.ValidLieTypeIndex) (Q : TauCeti.PrimePower), Odd m ∧ 2 ≤ m ∧ Q.p = 2 ∧
          Q.exponent = m ∧ d.1 = .A 2 Q ∧
          Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) ∧
          ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = mRankChev d.1 r 1) ∨
        (IsLThreeOfExp 1 ↥(barO2 L) ∧
          ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L = if r = 3 ∨ r = 7 then 1 else 0)) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hoddK : Odd (Nat.card (Subgroup.center ↥(barO2 L))) := centre_barO2_odd hL.1
  rcases hdat with ⟨d, hrt, hin, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ |
    ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩ | ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩
  · have h3 : CFSG.Open.pRank 3 L =
        mRankChev d.1 3 (Nat.card (Subgroup.center ↥(barO2 L))) :=
      hr 3 Nat.prime_three (by norm_num)
    rw [h] at h3
    have hone : RankOneList d.1 := ((mRank3_cases hrt _).1).1 h3.symm
    obtain ⟨Q, hQd, hodd⟩ := rankOneList_cases hone
    have hQp : Q.p = 2 := by
      have := hrt
      rw [hQd] at this
      exact this.1
    have hexp : 2 ≤ Q.exponent := two_le_exponent_of_A2 hQp hQd
    have hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
      (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).1 (Or.inl ⟨Q, hQp, hodd, hQd⟩)
    refine ⟨hZ, Or.inl ⟨Q.exponent, d, Q, hodd, hexp, hQp, rfl, hQd, ⟨e⟩, ?_⟩⟩
    intro r hr' hr2
    rw [hr r hr' hr2, hZ]
  · exfalso
    have h3 := hr 3 Nat.prime_three (by norm_num)
    rw [h] at h3
    rcases hn with rfl | rfl <;> omega
  · exfalso
    have h3 := hr 3 Nat.prime_three (by norm_num)
    rw [h] at h3
    rcases hn with rfl | rfl <;> omega
  · have hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
      (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).1 (Or.inr ⟨q, hq, hd⟩)
    have hZbot : Subgroup.center ↥(barO2 L) = ⊥ := Subgroup.card_eq_one.1 hZ
    refine ⟨hZ, Or.inr ⟨Or.inl ⟨rfl, d, q, hq, hd, ⟨?_⟩⟩, hr⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZbot).trans QuotientGroup.quotientBot).symm.trans
      (eQ.trans e)
  · exfalso
    have h3 := hr 3 Nat.prime_three (by norm_num)
    rw [h] at h3
    simp at h3

theorem centre_three_shape (hKSML3 : KSML3) (hKSMAlt : KSMAlt) (hKSMOdd : KSMOdd) (hKSMU4 : KSMU4)
    (hK541 : K541) {T T₁ T₂ : Subgroup X} {L : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    (hX : GNSetting X T) (hshape : GNShape T T₁ T₂) (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (hdat : RankDatum1512 T L Ls)
    (hA7 : Nonempty (↥Ls ≃* alternatingGroup (Fin 7)) →
      Nonempty (↥(barO2 L) ≃* alternatingGroup (Fin 7)))
    (h3 : 3 ∣ Nat.card (Subgroup.center ↥(barO2 L))) :
    Nat.card (Subgroup.center ↥(barO2 L)) = 3 ∧ CFSG.Open.pRank 3 L = 2 ∧
      ((∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (↥Ls ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))) ∨
        IsAltSixCoverThree ↥(barO2 L)) := by
  obtain ⟨⟨eQ⟩, -, -⟩ := centre_of_lift hX hLs.1 hL
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hoddK : Odd (Nat.card (Subgroup.center ↥(barO2 L))) := centre_barO2_odd hL.1
  have hcomm : ⁅Ls, gnImg T (CFSG.Quasithin.thompsonJ T)⁆ = Ls := (hshape Ls hLs).1
  rcases hdat with ⟨d, hrt, hin, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ | ⟨n, hn, ⟨e⟩, hr⟩ |
    ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩ | ⟨⟨d, q, hq, hd, ⟨e⟩⟩, hr⟩
  · by_cases hA2 : ∃ Q : TauCeti.PrimePower, d.1 = .A 2 Q
    · obtain ⟨Q, hQ⟩ := hA2
      have hQp : Q.p = 2 := by
        have := hrt
        rw [hQ] at this
        exact this.1
      rcases Nat.even_or_odd Q.exponent with hev | hodd
      · have hdvd : Nat.card (Subgroup.center ↥(barO2 L)) ∣ 3 :=
          (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).2 ⟨Q, hQp, hev, hQ⟩
        have hZ3 : Nat.card (Subgroup.center ↥(barO2 L)) = 3 := Nat.dvd_antisymm hdvd h3
        have hexp : 2 ≤ Q.exponent := two_le_exponent_of_A2 hQp hQ
        refine ⟨hZ3, ?_, Or.inl ⟨Q.exponent, by omega, hev, ?_⟩⟩
        · rw [hr 3 Nat.prime_three (by norm_num)]
          exact ((mRank3_cases hrt _).2.1).2 (by rw [hQ]; exact hev)
        · exact hK541 X T hX Ls hLs.1 hcomm Q.exponent
            (Or.inr ⟨hexp, d, Q, hQp, rfl, hQ, ⟨e⟩⟩)
      · exfalso
        have := (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).1 (Or.inl ⟨Q, hQp, hodd, hQ⟩)
        rw [this] at h3
        omega
    · push Not at hA2
      by_cases hU4 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 3 Q
      · exfalso
        obtain ⟨Q, hQ⟩ := hU4
        have hQp : Q.p = 2 := by
          have := hrt
          rw [hQ] at this
          exact this.1
        have := hKSMU4 ↥(barO2 L) hK d ⟨Q, hQp, hQ⟩ ⟨eQ.trans e⟩ hoddK
        rw [this] at h3
        omega
      · push Not at hU4
        exfalso
        have hk := hKSMOdd.1 ↥(barO2 L) hK d hin hA2 hU4 ⟨eQ.trans e⟩ hoddK
        by_cases hU5 : ∃ Q : TauCeti.PrimePower, d.1 = .twistedA 4 Q
        · have h5 := hk.1 hU5
          have h35 : 3 ∣ 5 := h3.trans h5
          omega
        · push Not at hU5
          have := hk.2 hU5
          rw [this] at h3
          omega
  · rcases hn with rfl | rfl
    · have hdvd : Nat.card (Subgroup.center ↥(barO2 L)) ∣ 3 :=
        (hKSMAlt ↥(barO2 L) hK 6 ⟨eQ.trans e⟩ hoddK).1 (Or.inl rfl)
      have hZ3 : Nat.card (Subgroup.center ↥(barO2 L)) = 3 := Nat.dvd_antisymm hdvd h3
      refine ⟨hZ3, ?_, Or.inr ⟨hK, hZ3, ⟨eQ.trans e⟩⟩⟩
      rw [hr 3 Nat.prime_three (by norm_num)]
    · exfalso
      have := (hKSMAlt ↥(barO2 L) hK 8 ⟨eQ.trans e⟩ hoddK).2 (by norm_num)
      rw [this] at h3
      omega
  · exfalso
    rcases hn with rfl | rfl
    · have := centre_barO2_eq_bot_of_A7 (hA7 ⟨e⟩)
      rw [this] at h3
      omega
    · obtain ⟨-, ⟨e''⟩⟩ := quotCenter_equiv_alt (n := 10) (by norm_num) e
      have := (hKSMAlt ↥(barO2 L) hK 10 ⟨eQ.trans e''⟩ hoddK).2 (by norm_num)
      rw [this] at h3
      omega
  · exfalso
    have := (hKSML3 ↥(barO2 L) hK d ⟨eQ.trans e⟩ hoddK).1 (Or.inr ⟨q, hq, hd⟩)
    rw [this] at h3
    omega
  · exfalso
    have := hKSMOdd.2 ↥(barO2 L) hK d ⟨q, hq, hd⟩ ⟨eQ.trans e⟩ hoddK
    rw [this] at h3
    omega

theorem dvd_of_one_le_rkLin_three {m z p : ℕ} (hp : p.Prime)
    (h : 1 ≤ rkLin 3 true (2 ^ m) p z) : p ∣ (2 ^ (2 * m) - 1) * (2 ^ (3 * m) - 1) := by
  have hQ : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hpow := rank_eq_two_of_in1512_aux_dvd_pow (Q := 2 ^ m) (p := p) hQ
  unfold rkLin at h
  by_cases he : eP (2 ^ m) p = 1
  · have hd : p ∣ 2 ^ m - 1 := (eP_eq_one_iff hQ).1 he
    have h2 : 2 ^ m - 1 ∣ 2 ^ (2 * m) - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_mul_left m 2)
    exact (hd.trans h2).mul_right _
  · have h3 : 1 ≤ 3 / eP (2 ^ m) p := by simpa [he] using h
    have h4 : eP (2 ^ m) p ≠ 0 := by
      intro h0
      rw [h0] at h3
      simp at h3
    have h5 : eP (2 ^ m) p ≤ 3 := by
      by_contra hgt
      have : 3 / eP (2 ^ m) p = 0 := Nat.div_eq_of_lt (by omega)
      omega
    have h6 : eP (2 ^ m) p = 2 ∨ eP (2 ^ m) p = 3 := by omega
    rcases h6 with h6 | h6
    · rw [h6] at hpow
      have : (2 ^ m) ^ 2 = 2 ^ (2 * m) := (pow_mul' 2 2 m).symm
      rw [this] at hpow
      exact hpow.mul_right _
    · rw [h6] at hpow
      have : (2 ^ m) ^ 3 = 2 ^ (3 * m) := (pow_mul' 2 3 m).symm
      rw [this] at hpow
      exact hpow.mul_left _

theorem rkLin_three_true_eq_two {Q p z : ℕ} (hQ : 1 ≤ Q) (h : p ∣ Q - 1) (hp : p.Prime) :
    rkLin 3 true Q p z = 2 := by
  have h1 : eP Q p = 1 := (eP_eq_one_iff hQ).2 h
  unfold rkLin
  simp [h1]

theorem exists_odd_prime_dvd_two_pow_sub_one_s15 {m : ℕ} (hm : 2 ≤ m) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ m - 1 := by
  have h4 : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show 2 ^ m - 1 ≠ 1 by omega)
  refine ⟨p, hp, ?_, hpd⟩
  rintro rfl
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  omega

end TableLookups

end CFSG.LocalAnalysis.RankThreeUC.S15
