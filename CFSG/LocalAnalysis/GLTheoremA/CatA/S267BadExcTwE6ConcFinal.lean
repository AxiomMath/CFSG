module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Heads
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuterNF
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

namespace TwE6Outer

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem concA_of_twistedE6_of_outer (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) (hℓ2 : ℓ ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpQ : p ∣ ℓ ^ f - 1)
    (hdiag : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1)) (hS : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBc : Nat.card B = p ^ (4 + 2))
    (eX : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)), IsElemAbelian p F →
      Nat.card F ≤ p ^ 4) : S267ConcA p S B :=
  concA_of_twistedE6_of_outer_of_modelBGen hK hf hp hp2 hdiag (by norm_num) hS hcore hZ hB hBC
    hBc eX hX fun _ hε hout => modelBGen_twistedE6_of_dvd_sub_one hK hf hℓ2 hp hp2 hpQ hε hout

theorem concA_of_twistedE6_of_outer_of_dvd_add_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : p ∣ ℓ ^ f + 1) (hS : S.Normal)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBc : Nat.card B = p ^ (6 + 2))
    (eX : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≃* PSimple p S)
    (hX : ∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)), IsElemAbelian p F →
      Nat.card F ≤ p ^ 6) : S267ConcA p S B := by
  have hdiag : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) := fun h => by
    have := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))
    omega
  exact concA_of_twistedE6_of_outer_of_modelBGen hK hf hp (by omega) hdiag (by norm_num) hS hcore
    hZ hB hBC hBc eX hX fun _ hε hout => modelBGen_twistedE6_of_dvd_add_one hK hf hℓ2 hp hp5 hpQ hε
      hout

end TwE6Outer

theorem twE6OuterInput_holds : TwE6OuterInput := by
  intro Ω _ _ S B K _ _ ℓ f _ _ hK hf hℓ2 p hp hp2 hpQ hdiag hS hcore hZ hB hBC hBc eX hX
  exact TwE6Outer.concA_of_twistedE6_of_outer hK hf hℓ2 hp hp2 hpQ hdiag hS hcore hZ hB hBC hBc eX
    hX

open CFSG.Blueprint.Multiplier CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

theorem concA_badExcCore_twistedE6_of_outer {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hp3 : p ≠ 3)
    (hBc : Nat.card B = p ^ (if p ∣ Q.card - 1 then 6 else 8)) : S267ConcA p S B := by
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar
  subst hchar
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
    omega
  obtain ⟨K, _, σ, hK, hσ, ⟨ec⟩⟩ := exists_catEquiv_twistedE6 Q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero 2 (pow_ne_zero _ Q.prime_p.ne_zero))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K Q.p := charP_of_card_eq_prime_pow (f := Q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have hσ' : σ = unitaryInvolution K Q.p Q.exponent :=
    RingEquiv.ext fun c => (hσ c).trans (unitaryInvolution_apply K Q.p Q.exponent c).symm
  subst hσ'
  have hQ : Q.card = Q.p ^ Q.exponent := by rw [TauCeti.PrimePower.card_def]
  have hZ := center_eq_bot_of_twistedE6 hp hp3 hperf hcore hv hq2 e
  have hX : ∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K Q.p Q.exponent)),
      IsElemAbelian p F → Nat.card F ≤ p ^ (if p ∣ Q.p ^ Q.exponent - 1 then 4 else 6) :=
    card_le_pow_twistedE6 hK Q.exponent_pos hp hp5 (hQ ▸ hdvd)
  by_cases h1 : p ∣ Q.card - 1
  · rw [if_pos h1] at hBc
    have h1' : p ∣ Q.p ^ Q.exponent - 1 := hQ ▸ h1
    have hdiag : ¬ p ∣ Nat.gcd 3 (Q.p ^ Q.exponent + 1) := fun h =>
      hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h.trans (Nat.gcd_dvd_left _ _)))
    refine TwE6Outer.concA_of_twistedE6_of_outer hK Q.exponent_pos hq2 hp hp2 h1' hdiag hS hcore
      hZ hB hBC hBc (ec.symm.trans e.symm) fun F hF => ?_
    have h := hX F hF
    rwa [if_pos h1'] at h
  · rw [if_neg h1] at hBc
    have hQ1 : 1 ≤ Q.card :=
      Nat.one_le_iff_ne_zero.2 (by rw [hQ]; exact pow_ne_zero _ Q.prime_p.ne_zero)
    have h2 : p ∣ Q.card + 1 := by
      have e2 : Q.card ^ 2 - 1 = (Q.card + 1) * (Q.card - 1) := by
        have h3 : 1 ≤ Q.card ^ 2 := Nat.one_le_pow _ _ hQ1
        zify [hQ1, h3]
        ring
      rw [e2] at hdvd
      exact (hp.dvd_mul.1 hdvd).resolve_right h1
    have h1' : ¬ p ∣ Q.p ^ Q.exponent - 1 := hQ ▸ h1
    refine TwE6Outer.concA_of_twistedE6_of_outer_of_dvd_add_one hK Q.exponent_pos hq2 hp hp5
      (hQ ▸ h2) hS hcore hZ hB hBC hBc (ec.symm.trans e.symm) fun F hF => ?_
    have h := hX F hF
    rwa [if_neg h1'] at h

theorem concA_badExcCore_twistedE6_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hp3 : p ≠ 3) : S267ConcA p S B := by
  have h2 := card_le_pow_add_two_twistedE6 hp hp2 hq2 hS hperf hB hBC hv hchar e hdvd hp3
  rcases card_le_or_eq_of_le hp hB h2 with h | h
  · refine concA_badExcCore_twistedE6_of_dvd_of_card_le hp hp2 hq2 hS hperf hcore hB hBC hv hchar e
      hdvd hp3 ?_
    split_ifs at h ⊢ <;> exact h
  · refine concA_badExcCore_twistedE6_of_outer hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hdvd hp3
      ?_
    split_ifs at h ⊢ <;> exact h

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
