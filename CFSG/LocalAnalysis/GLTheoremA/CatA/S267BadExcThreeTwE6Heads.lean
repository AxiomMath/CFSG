module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Out
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6Conc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc


@[expose] def TwE6OuterInput : Prop :=
  ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {K : Type} [Field K] [Finite K] {ℓ f : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ], Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → ∀ {p : ℕ}, p.Prime →
    p ≠ 2 → p ∣ ℓ ^ f - 1 → ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) → S.Normal → GLAPPrimeCore p ↥S = ⊥ →
    Subgroup.center ↥S = ⊥ → IsElemAbelian p B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
    Nat.card B = p ^ (4 + 2) →
    (↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≃* PSimple p S) →
    (∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)), IsElemAbelian p F →
      Nat.card F ≤ p ^ 4) → S267ConcA p S B

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

open CFSG.Blueprint.Multiplier CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge

theorem center_eq_bot_of_twistedE6_of_not_dvd {p : ℕ} (hp : p.Prime) {Q : TauCeti.PrimePower}
    (hpg : ¬ p ∣ Nat.gcd 3 (Q.p ^ Q.exponent + 1)) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hQ2 : Q.p ≠ 2) (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) :
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
  exact hpg

theorem card_le_three_pow_six_twistedE6_of_mod_one (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) {K : Type}
    [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hf : 1 ≤ f) (hQ3 : ℓ ^ f % 3 = 1)
    (eX : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) ≃* PSimple 3 S) :
    Nat.card B ≤ 3 ^ (4 + 2) := by
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ0, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK
      (unitaryInvolution K ℓ f) (unitaryInvolution_apply K ℓ f)
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_twistedE6_three hℓ hf K hK (unitaryInvolution K ℓ f)
    (unitaryInvolution_apply K ℓ f) (by omega)
  have hF₀ : Nat.card (GaloisField ℓ f) = ℓ ^ f := GaloisField.card ℓ f (by omega)
  exact card_le_pow_add_two_of_hom Nat.prime_three hS hperf hB hBC eX hZ0 Θ hΘ fun F hF =>
    card_le_pow_four_twistedE6_three_of_mod_one hF₀ hK _ (unitaryInvolution_apply K ℓ f) hQ3 hF

theorem concA_badExcCore_twistedE6_three_of_mod_one_of_outer (houter : TwE6OuterInput)
    {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) (hp3 : p = 3)
    (h3 : 3 ∣ Q.card - 1) : S267ConcA p S B := by
  subst hp3
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar
  subst hchar
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
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
  have hQ1 : 1 ≤ Q.p ^ Q.exponent := Nat.one_le_pow _ _ Q.prime_p.pos
  have h31 : 3 ∣ Q.p ^ Q.exponent - 1 := by rw [← hQ]; exact h3
  have hQ3 : Q.p ^ Q.exponent % 3 = 1 := by omega
  have hg : ¬ 3 ∣ Nat.gcd 3 (Q.p ^ Q.exponent + 1) := fun h => by
    have := h.trans (Nat.gcd_dvd_right _ _)
    omega
  have hZ := center_eq_bot_of_twistedE6_of_not_dvd Nat.prime_three hg hperf hcore hv hq2 e
  set eX := ec.symm.trans e.symm with heX
  have hX : ∀ F : Subgroup ↥(twistedE6RootGroup K (unitaryInvolution K Q.p Q.exponent)),
      IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 4 := fun F hF =>
    card_le_pow_four_twistedE6_three_of_mod_one (F₀ := GaloisField Q.p Q.exponent)
      (GaloisField.card _ _ Q.exponent_pos.ne') hK _
      (unitaryInvolution_apply K Q.p Q.exponent) hQ3 hF
  rcases card_le_or_eq_of_le Nat.prime_three hB
      (card_le_three_pow_six_twistedE6_of_mod_one hS hperf hB hBC hK Q.exponent_pos hQ3 eX)
    with hle | heq
  · set eS : PSimple 3 S ≃* ↥S := (psimpleEquivCenterQuotOfCore hcore).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) with heS
    set φ : ↥(twistedE6RootGroup K (unitaryInvolution K Q.p Q.exponent)) →* Ω :=
      S.subtype.comp (eX.trans eS).toMonoidHom with hφdef
    have hφ : Function.Injective φ := S.subtype_injective.comp (eX.trans eS).injective
    have hφS : φ.range = S := by
      rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (eX.trans eS).surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact ModelGen.concA_of_modelAGen Nat.prime_three (by norm_num) hS hcore hZ hB hBC hle φ hφ hφS
      (modelAGen_twistedE6_of_dvd_sub_one hK Q.exponent_pos hq2 Nat.prime_three (by norm_num) h31)
  · exact houter hK Q.exponent_pos hq2 Nat.prime_three (by norm_num) h31 hg hS hcore hZ hB hBC heq
      eX hX

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
