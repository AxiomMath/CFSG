module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcCoreDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcDvdHeads
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcExcDispatchAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Heads
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcFinal
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6One

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4


theorem s267FactBadExcCore_of_heads
    (h2E6threePlus : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid),
        (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) →
        p ∣ Q.card ^ 2 - 1 → p = 3 → 3 ∣ Q.card + 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B) :
    S267FactBadExcCore := by
  have key : ∀ n : ℕ, 0 < n → 3 ∣ n ^ 2 - 1 → ¬ 3 ∣ n - 1 → 3 ∣ n + 1 := by
    intro n hn hd h1
    have h2 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
    · have : n ^ 2 % 3 = 0 := by rw [Nat.pow_mod, h]
      omega
    · omega
    · omega
  have hQ1 : ∀ Q : TauCeti.PrimePower, 0 < Q.card := fun Q => by
    rw [TauCeti.PrimePower.card_def]
    exact pow_pos Q.prime_p.pos _
  refine s267FactBadExcCore_of_dvd
    (badExcCore_dvd_of_twistedE6_of_three concA_badExcCore_twistedE6_of_dvd
      concA_badExcCore_E6_three_of_mod_one ?_ ?_) ?_
  ·
    intro p q hp _ _ hq2 _ Ω _ _ _ S B hS hperf hcore hB _ _ _ hBC _ Q hv hchar e hd hp3 h1 _
    subst hp3
    exact Or.inl (concA_badExcCore_E6_three_of_mod_two hp hq2 hS hperf hcore hB hBC hv hchar e rfl
      (key _ (hQ1 Q) hd h1))
  ·
    intro p q hp hp2 hq hq2 hqp Ω _ _ hK S B hS hperf hcore hB hSB hrank hB4 hBC hp3B Q hv hchar e
      hd hp3 hHq
    subst hp3
    by_cases h1 : 3 ∣ Q.card - 1
    · exact Or.inl (concA_badExcCore_twistedE6_three_of_mod_one_of_outer twE6OuterInput_holds hp
        hq2 hS hperf hcore hB hBC hv hchar e rfl h1)
    · exact h2E6threePlus hp hp2 hq hq2 hqp hK hS hperf hcore hB hSB hrank hB4 hBC hp3B hv hchar e
        hd rfl (key _ (hQ1 Q) hd h1) hHq
  ·
    intro p q hp _ _ hq2 hqp Ω _ _ _ S B hS hperf _ hB _ _ _ hBC _ Q hv hchar e _ h4 hHq
    refine (false_of_badExcCore_E8_of_not_dvd_all hp hq2 hqp hS hperf hB hBC hv hchar e ?_
      hHq).elim
    intro hd
    have hQ : 1 ≤ Q.card ^ 2 := Nat.one_le_pow _ _ (hQ1 Q)
    have h1 : ((Q.card : ℕ) : ZMod p) ^ 2 = 1 := by
      have h0 := (ZMod.natCast_eq_zero_iff (Q.card ^ 2 - 1) p).2 hd
      rw [Nat.cast_sub hQ, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
      exact h0
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [h4] at h2
    omega

theorem s267FactBadExcLie_of_heads
    (h2E6threePlus : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid),
        (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) →
        p ∣ Q.card ^ 2 - 1 → p = 3 → 3 ∣ Q.card + 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B) :
    S267FactBadExcLie :=
  s267FactBadExcLie_of_core (s267FactBadExcCore_of_heads h2E6threePlus)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
