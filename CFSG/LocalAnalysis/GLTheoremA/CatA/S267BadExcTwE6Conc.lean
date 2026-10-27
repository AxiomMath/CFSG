module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConc
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc


section Witness

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem natCast_ne_zero_of_dvd_sq (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime)
    (hpQ : p ∣ (ℓ ^ f) ^ 2 - 1) : (p : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  have hpℓ : p = ℓ := ((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h).symm
  have h1 : ℓ ∣ (ℓ ^ f) ^ 2 := dvd_pow (dvd_pow_self ℓ (by omega)) two_ne_zero
  have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos f)
  rw [hpℓ] at hpQ
  have h3 : ℓ ∣ 1 := by
    have := Nat.dvd_sub h1 hpQ
    rwa [Nat.sub_sub_self h2] at this
  exact (Fact.out : ℓ.Prime).not_dvd_one h3

theorem exists_orderOf_units_eq (hK : Nat.card K = (ℓ ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hpQ : p ∣ (ℓ ^ f) ^ 2 - 1) : ∃ c : Kˣ, orderOf c = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : Nat.card Kˣ = Nat.card K - 1 := by
    classical
    haveI : Fintype K := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  exact exists_prime_orderOf_dvd_card' p (by rw [hc, hK]; exact hpQ)

theorem modelAGen_twistedE6_of_dvd_sub_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpQ : p ∣ ℓ ^ f - 1) :
    ModelGen.ModelAGen p 4 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hQ1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hpQ2 : p ∣ (ℓ ^ f) ^ 2 - 1 := hpQ.trans (Nat.sub_one_dvd_pow_sub_one _ 2)
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hq5 : 5 ≤ ℓ ^ f := by
    have hℓ3 : 3 ≤ ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
    have hodd : Odd (ℓ ^ f) := (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
    have hle : p ≤ ℓ ^ f - 1 := Nat.le_of_dvd (by
      have : 3 ≤ ℓ ^ f := hℓ3.trans (Nat.le_self_pow (by omega) ℓ)
      omega) hpQ
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 6 _) ?_
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => hp2 ?_
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub h hpQ
      rwa [show ℓ ^ f + 1 - (ℓ ^ f - 1) = 2 by omega] at this
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  have hpSU := dvd_card_su_two (K := K) (ℓ := ℓ) (f := f) hK hpQ2
  obtain ⟨M, hM⟩ := exists_prime_orderOf_dvd_card' p hpSU
  obtain ⟨c, hc⟩ := exists_orderOf_units_eq hK hp hpQ2
  have hcQ : (c : K) ^ (ℓ ^ f) = c := by
    obtain ⟨k, hk⟩ := hpQ
    have h1 : c ^ (ℓ ^ f - 1) = 1 := by rw [hk, pow_mul, ← hc, pow_orderOf_eq_one, one_pow]
    have h2 : c ^ (ℓ ^ f) = c := by
      calc c ^ (ℓ ^ f) = c ^ (ℓ ^ f - 1) * c := by rw [← pow_succ, Nat.sub_add_cancel hQ1]
        _ = c := by rw [h1, one_mul]
    rw [← Units.val_pow_eq_pow_val, h2]
  have hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [map_add, unitaryInvolution_apply, unitaryInvolution_apply, hcQ, Units.val_inv_eq_inv_val,
      inv_pow, hcQ]
  obtain ⟨ζ, hζ, hσζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 6
  exact modelAGen_twistedE6 hK hf hζ hσζ P hP hℓ2 hq5 hp hp2 (natCast_ne_zero_of_dvd_sq hf hp hpQ2)
    hcop hpSU hc hct (blockTripleHom_injective M hM) (blockTripleHom_single_mem M hM)
    (fun h => one_ne_zero (Multiplicative.ofAdd.injective
      ((congrFun h 0).symm.trans (Pi.mulSingle_eq_same _ _)).symm))

theorem modelAGen_twistedE6_of_dvd_add_one (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : p ∣ ℓ ^ f + 1) :
    ModelGen.ModelAGen p 6 ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := Fact.out
  have hQ1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hpQ2 : p ∣ (ℓ ^ f) ^ 2 - 1 := by
    have h : (ℓ ^ f) ^ 2 - 1 = (ℓ ^ f + 1) * (ℓ ^ f - 1) := by
      have h2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [hQ1, h2]
      ring
    rw [h]
    exact hpQ.mul_right _
  have hq5 : 5 ≤ ℓ ^ f := by
    have hℓ3 : 3 ≤ ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
    have hodd : Odd (ℓ ^ f) := (hℓ.eq_two_or_odd'.resolve_left hℓ2).pow
    have hle : p ≤ ℓ ^ f + 1 := Nat.le_of_dvd (by omega) hpQ
    obtain ⟨k, hk⟩ := hodd
    omega
  have hcop : Nat.Coprime p (Nat.gcd 6 (ℓ ^ f + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 6 _) ?_
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
    have h6 := Nat.le_of_dvd (by norm_num) h
    have h56 : p = 5 ∨ p = 6 := by omega
    rcases h56 with rfl | rfl
    · norm_num at h
    · exact absurd hp (by norm_num)
  have hpSU := dvd_card_su_two (K := K) (ℓ := ℓ) (f := f) hK hpQ2
  obtain ⟨c, hc⟩ := exists_orderOf_units_eq hK hp hpQ2
  have h2u : c ^ (ℓ ^ f) = c⁻¹ := by
    obtain ⟨k, hk⟩ := hpQ
    have h1 : c ^ (ℓ ^ f + 1) = 1 := by rw [hk, pow_mul, ← hc, pow_orderOf_eq_one, one_pow]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h1])
  have hcQ : (c : K) ^ (ℓ ^ f) = ((c⁻¹ : Kˣ) : K) := by rw [← Units.val_pow_eq_pow_val, h2u]
  have hcQ' : ((c⁻¹ : Kˣ) : K) ^ (ℓ ^ f) = (c : K) := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, h2u, inv_inv]
  have hct : unitaryInvolution K ℓ f ((c : K) + ((c⁻¹ : Kˣ) : K)) = (c : K) + ((c⁻¹ : Kˣ) : K) := by
    rw [map_add, unitaryInvolution_apply, unitaryInvolution_apply, hcQ, hcQ', add_comm]
  obtain ⟨ζ, hζ, hσζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hK 6
  exact modelAGen_twistedE6 hK hf hζ hσζ P hP hℓ2 hq5 hp (by omega)
    (natCast_ne_zero_of_dvd_sq hf hp hpQ2) hcop hpSU hc hct (diagSUHom_injective c hc hpQ)
    (diagSUHom_diagGen_mem c hc hpQ) diagGen_ne_one

theorem card_le_pow_twistedE6 (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : p ∣ (ℓ ^ f) ^ 2 - 1)
    (F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) (hF : IsElemAbelian p F) :
    Nat.card F ≤ p ^ (if p ∣ ℓ ^ f - 1 then 4 else 6) := by
  have hℓ : ℓ.Prime := Fact.out
  have hpq : ¬ p ∣ ℓ ^ f := fun h => by
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos hℓ.pos f)
    have h2 : p ∣ (ℓ ^ f) ^ 2 := dvd_pow h two_ne_zero
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hpQ
      rwa [Nat.sub_sub_self h1] at this
    exact hp.not_dvd_one h3
  split_ifs with h1
  · haveI : Fact p.Prime := ⟨hp⟩
    have he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 1 := by
      rw [orderOf_eq_one_iff]
      have hQ1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
      have h2 := (ZMod.natCast_eq_zero_iff (ℓ ^ f - 1) p).2 h1
      rw [Nat.cast_sub hQ1, Nat.cast_one, sub_eq_zero] at h2
      exact h2
    exact (CFSG.StandardType.ExcFrames.sylowTorus_twistedE6_one hℓ hf K hK
      (unitaryInvolution K ℓ f) (unitaryInvolution_apply K ℓ f) hp hp5 hpq he).rank_le hp hF
  ·
    have hle : twistedE6RootGroup K (unitaryInvolution K ℓ f) ≤ adjointGroup Tag.E6 K :=
      (graphFixedRootGroup_le _ _ _).trans inf_le_left
    set ι₀ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →* ↥(adjointGroup Tag.E6 K) :=
      MonoidHom.mk' (fun x => ⟨(x : ModGL TwistTag.E6.tag K), hle x.2⟩) (fun _ _ => rfl) with hι₀
    have hι₀inj : Function.Injective ι₀ := fun x y h => Subtype.ext (by
      have h' := congrArg Subtype.val h
      exact h')
    have hF' := CFSG.SectionRank.isElemAbelian_map hF ι₀
    have hc := card_le_pow_rank_E6_of_dvd_sub_one (K := K) hp hp5 (by rw [hK]; exact hpQ)
      (F.map ι₀) hF'
    rwa [Subgroup.card_map_of_injective hι₀inj] at hc

end Witness

section Head


open CFSG.Blueprint.Multiplier CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem center_eq_bot_of_twistedE6 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) (hQ2 : Q.p ≠ 2)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) :
    Subgroup.center ↥S = ⊥ := by
  have hmodel : CFSG.Models.LieModel (Cat ⟨.twistedE6 Q, hv⟩) .twistedE6 0 Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, rfl⟩,
      Or.inr ⟨rfl, ⟨.twistedE6 Q, hv⟩, ⟨rfl, rfl⟩, ⟨MulEquiv.refl _⟩⟩⟩
  have hq3 : 3 ≤ Q.p ^ Q.exponent :=
    (lt_of_le_of_ne Q.prime_p.two_le (Ne.symm hQ2)).trans_le
      (Nat.le_self_pow Q.exponent_pos.ne' _)
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessExceptional.twistedE6_row hmodel hq3
  refine center_eq_bot_of_multiplier hp hperf hcore e ?_
  rw [Nat.card_congr eM.toEquiv]
  have hex : exceptionalOrders .twistedE6 0 Q.p Q.exponent = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, genericOrders, mul_one]
  intro h
  have h1 : p ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1)

theorem card_le_pow_add_two_twistedE6 {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hp3 : p ≠ 3) :
    Nat.card B ≤ p ^ ((if p ∣ Q.card - 1 then 4 else 6) + 2) := by
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
  have hQ : Q.card = Q.p ^ Q.exponent := by rw [TauCeti.PrimePower.card_def]
  obtain ⟨Θ, hΘ⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_ringAut_twistedE6
    Q.prime_p Q.exponent_pos K hK σ hσ hp hp3
  have hσ' : σ = unitaryInvolution K Q.p Q.exponent :=
    RingEquiv.ext fun c => (hσ c).trans (unitaryInvolution_apply K Q.p Q.exponent c).symm
  subst hσ'
  haveI : IsCyclic (RingAut K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hZX : Subgroup.center ↥(twistedE6RootGroup K (unitaryInvolution K Q.p Q.exponent)) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (unitaryInvolution K Q.p Q.exponent).surjective
  have h := card_le_pow_add_two_of_hom hp hS hperf hB hBC (ec.symm.trans e.symm) hZX Θ hΘ
    (card_le_pow_twistedE6 hK Q.exponent_pos hp hp5 (hQ ▸ hdvd))
  rwa [← hQ] at h

theorem concA_badExcCore_twistedE6_of_dvd_of_card_le {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (hdvd : p ∣ Q.card ^ 2 - 1) (hp3 : p ≠ 3)
    (hBle : Nat.card B ≤ p ^ (if p ∣ Q.card - 1 then 5 else 7)) : S267ConcA p S B := by
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
  set eS : PSimple p S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
  set eX := ec.symm.trans e.symm with heX
  set φ : ↥(twistedE6RootGroup K (unitaryInvolution K Q.p Q.exponent)) →* Ω :=
    S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
  have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
  have hφS : φ.range = S := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  by_cases h1 : p ∣ Q.card - 1
  · rw [if_pos h1] at hBle
    exact ModelGen.concA_of_modelAGen hp (by norm_num) hS hcore hZ hB hBC hBle φ hφ hφS
      (modelAGen_twistedE6_of_dvd_sub_one hK Q.exponent_pos hq2 hp hp2 (hQ ▸ h1))
  · rw [if_neg h1] at hBle
    have hQ1 : 1 ≤ Q.card := Nat.one_le_iff_ne_zero.2 (by rw [hQ]; exact pow_ne_zero _ Q.prime_p.ne_zero)
    have h2 : p ∣ Q.card + 1 := by
      have e2 : Q.card ^ 2 - 1 = (Q.card + 1) * (Q.card - 1) := by
        have h3 : 1 ≤ Q.card ^ 2 := Nat.one_le_pow _ _ hQ1
        zify [hQ1, h3]
        ring
      rw [e2] at hdvd
      exact (hp.dvd_mul.1 hdvd).resolve_right h1
    exact ModelGen.concA_of_modelAGen hp (by norm_num) hS hcore hZ hB hBC hBle φ hφ hφS
      (modelAGen_twistedE6_of_dvd_add_one hK Q.exponent_pos hq2 hp hp5 (hQ ▸ h2))

end Head

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
