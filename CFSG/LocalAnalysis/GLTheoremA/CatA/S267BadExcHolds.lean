module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcCoreDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcExcDispatch
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTriD4Hq
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6Two

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LieType.SeitzGeneration


theorem s267FactBadExcCore_of_dvd
    (hdvd : ∀ (mk : TauCeti.PrimePower → TauCeti.LieTypeIndex),
      mk = .F4 ∨ mk = .E6 ∨ mk = .twistedE6 ∨ mk = .E7 ∨ mk = .E8 →
      ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (mk Q).Valid), (mk Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨mk Q, hv⟩).Group) → p ∣ Q.card ^ 2 - 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B)
    (hE8 : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid),
        (TauCeti.LieTypeIndex.E8 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group) → p = 5 →
        orderOf ((Q.card : ℕ) : ZMod p) = 4 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B) :
    S267FactBadExcCore := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hSn hperf hcore hcat hB hSB hrank hB4 hBC hp3B hHq
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic r hr => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨d, hv⟩ := d
    obtain ⟨hchar, hcd⟩ := hi
    cases d with
    | G2 Q =>
      exact (false_of_badExcCore_G2 hp hp2 hq2 hqp hSn hperf hB hB4 hBC hp3B hv hchar e hHq).elim
    | trialityD4 Q =>
      exact (false_of_badExcCore_trialityD4 hp hp2 hq2 hqp hSn hperf hB hB4 hBC hp3B hv hchar e
        hHq).elim
    | F4 Q =>
      by_cases hd : p ∣ Q.card ^ 2 - 1
      · exact hdvd _ (Or.inl rfl) hp hp2 hq hq2 hqp hK hSn hperf hcore hB hSB hrank hB4 hBC hp3B
          hv hchar e hd hHq
      · exact (false_of_badExcCore_F4_of_not_dvd hp hq2 hqp hSn hperf hB hB4 hBC hv hchar e hd
          hHq).elim
    | E6 Q =>
      by_cases hd : p ∣ Q.card ^ 2 - 1
      · exact hdvd _ (Or.inr (Or.inl rfl)) hp hp2 hq hq2 hqp hK hSn hperf hcore hB hSB hrank hB4
          hBC hp3B hv hchar e hd hHq
      · exact (false_of_badExcCore_E6_of_not_dvd hp hq2 hqp hSn hperf hB hBC hv hchar e hd
          hHq).elim
    | twistedE6 Q =>
      by_cases hd : p ∣ Q.card ^ 2 - 1
      · exact hdvd _ (Or.inr (Or.inr (Or.inl rfl))) hp hp2 hq hq2 hqp hK hSn hperf hcore hB hSB
          hrank hB4 hBC hp3B hv hchar e hd hHq
      · by_cases h6 : orderOf ((Q.card : ℕ) : ZMod p) = 6 ∧ ¬ p ∣ Q.exponent ∧ Q.exponent ≤ 4
        ·
          exfalso
          rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar
          subst hchar
          have hpq : p ≠ Q.p := Ne.symm hqp
          have he := three_le_orderOf_of_not_dvd hp (not_dvd_card_of_ne hp hpq) hd
          have hrk := pRank_mulAut_le_twistedE6 Q hv e hp hpq he
          rw [h6.1, if_neg h6.2.1, show max 1 (degCountTw 6) + 0 = 3 by decide] at hrk
          have hBle := card_le_pow_succ_of_pRank_mulAut_le hp hSn hperf hB hBC hrk
          exact false_of_hq_of_lift (r := 5)
            ((pRank_le_of_card_le_pow hp hBle).trans_lt (by norm_num)) hHq e
            fun X _ _ φ hφ => five_le_twoLocalRank_cat_twistedE6 Q hv hq2 φ hφ
        · exact (false_of_badExcCore_twistedE6_of_not_dvd hp hq2 hqp hSn hperf hB hB4 hBC hv
            hchar e hd h6 hHq).elim
    | E7 Q =>
      by_cases hd : p ∣ Q.card ^ 2 - 1
      · exact hdvd _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp hp2 hq hq2 hqp hK hSn hperf hcore
          hB hSB hrank hB4 hBC hp3B hv hchar e hd hHq
      · exact (false_of_badExcCore_E7_of_not_dvd hp hq2 hqp hSn hperf hB hBC hv hchar e hd
          hHq).elim
    | E8 Q =>
      by_cases hd : p ∣ Q.card ^ 2 - 1
      · exact hdvd _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hp hp2 hq hq2 hqp hK hSn hperf hcore
          hB hSB hrank hB4 hBC hp3B hv hchar e hd hHq
      · by_cases h54 : p = 5 ∧ orderOf ((Q.card : ℕ) : ZMod p) = 4
        · exact hE8 hp hp2 hq hq2 hqp hK hSn hperf hcore hB hSB hrank hB4 hBC hp3B hv hchar e
            h54.1 h54.2 hHq
        · exact (false_of_badExcCore_E8_of_not_dvd hp hq2 hqp hSn hperf hB hBC hv hchar e hd h54
            hHq).elim
    | A n Q => exact hcd.elim
    | twistedA n Q => exact hcd.elim
    | B n Q => exact hcd.elim
    | C n Q => exact hcd.elim
    | D n Q => exact hcd.elim
    | twistedD n Q => exact hcd.elim
    | suzuki m => exact hcd.elim
    | reeF4 m => exact hcd.elim
    | tits => exact hcd.elim
    | reeG2 m => exact hcd.elim

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
