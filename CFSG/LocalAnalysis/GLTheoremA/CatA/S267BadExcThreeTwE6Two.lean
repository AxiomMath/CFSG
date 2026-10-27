module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Input
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Image
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Outer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6Central
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeTwE6VtwHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6One
import CFSG.GH74.Uniqueness.SU.SU7Gen3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)

section Inndiag

variable {ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem card_le_three_mul_card_inf_twInndiag (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {A : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hA : IsElemAbelian 3 A) :
    Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ)) := by
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  haveI : Finite (RingAut K) :=
    Finite.of_injective (fun δ : RingAut K => (δ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Θ A
  rw [hker] at h
  have h1 : Nat.card (A.map Θ) ≤ 3 := by
    refine CFSG.LocalAnalysis.RankFourTheoremC.card_le_of_isCyclic_of_pow_eq_one (by norm_num)
      fun y => ?_
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hxy, ← map_pow, hA.2 x hx, map_one]
  rw [← h]
  exact Nat.mul_le_mul_right _ h1

end Inndiag

section Split

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_twistedE6_three_of_pSimple (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
    (hℓ2 : ℓ ≠ 2) (h3 : 3 ∣ ℓ ^ f + 1) (hS : S.Normal) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
    {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))}
    (hΓe : ∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
      e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩))
    (hΓker : Γ.ker = centModSubgroup 3 S)
    (hR1 : B.map Γ ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
        twistedE6Diag K (unitaryInvolution K ℓ f) →
      3 ^ 6 ≤ Nat.card ↥(B.map Γ) → S267ConcA 3 S B)
    (hR2 : ∀ b ∈ B, Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
        twistedE6Diag K (unitaryInvolution K ℓ f) →
      3 ^ 6 ≤ Nat.card ↥(B.map Γ ⊓ (twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
        twistedE6Diag K (unitaryInvolution K ℓ f))) → S267ConcA 3 S B)
    (hc1 : Subgroup.center ↥S ≠ ⊥ → Nat.card B ≤ 3 ^ 6 → S267ConcA 3 S B)
    (hc2 : Subgroup.center ↥S ≠ ⊥ → Nat.card B ≤ 3 ^ 7 → ∀ b ∈ B,
      Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f) →
      S267ConcA 3 S B) :
    S267ConcA 3 S B := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) := Subtype.finite
  haveI : Finite (MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) :=
    Finite.of_injective (fun α : MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) =>
      (α : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →
        ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))) fun _ _ h => MulEquiv.ext (congrFun h)
  have hĀ : IsElemAbelian 3 (B.map Γ) := CFSG.SectionRank.isElemAbelian_map hB Γ
  have hĀle := card_le_three_mul_card_inf_twInndiag hℓ hf hK _ (unitaryInvolution_apply K ℓ f) hĀ
  set I := twistedE6Inn K (unitaryInvolution K ℓ f) ⊔ twistedE6Diag K (unitaryInvolution K ℓ f)
    with hIdef
  have hBΓ : Nat.card B = Nat.card (B.map Γ) * 3 := E6One.card_eq_card_map_mul_three hΓker hBC
  by_cases h6 : 3 ^ 6 ≤ Nat.card ↥(B.map Γ ⊓ I)
  ·
    by_cases hout : ∃ b ∈ B, Γ b ∉ I
    · obtain ⟨b, hb, hbI⟩ := hout
      exact hR2 b hb hbI h6
    · push Not at hout
      have hI : B.map Γ ≤ I := by
        rintro _ ⟨b, hb, rfl⟩
        exact hout b hb
      exact hR1 hI (h6.trans (Subgroup.card_le_of_le inf_le_left))
  have h5 := E6One.card_le_pow_five_of_not_le (hĀ.mono inf_le_left) h6
  have h7 : Nat.card B ≤ 3 ^ 7 := by
    rw [hBΓ]
    calc Nat.card (B.map Γ) * 3 ≤ 3 * 3 ^ 5 * 3 :=
          Nat.mul_le_mul_right _ (hĀle.trans (Nat.mul_le_mul_left _ h5))
      _ = 3 ^ 7 := by norm_num
  have h6' : (∀ b ∈ B, Γ b ∈ I) → Nat.card B ≤ 3 ^ (5 + 1) := fun hout => by
    have hI : B.map Γ ≤ I := by
      rintro _ ⟨b, hb, rfl⟩
      exact hout b hb
    rw [inf_eq_left.2 hI] at h5
    rw [hBΓ]
    calc Nat.card (B.map Γ) * 3 ≤ 3 ^ 5 * 3 := Nat.mul_le_mul_right _ h5
      _ = 3 ^ (5 + 1) := by norm_num
  by_cases hZ : Subgroup.center ↥S = ⊥
  ·
    have hinj : Function.Injective (chevQuotHom 3 S) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
      exact E6One.chevQuotHom_ker_le_center hcore
    set eS : ↥S ≃* PSimple 3 S :=
      MulEquiv.ofBijective (chevQuotHom 3 S) ⟨hinj, chevQuotHom_surjective 3 S⟩ with heS
    set φ : ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)) →* Ω :=
      S.subtype.comp (e.symm.trans eS.symm).toMonoidHom with hφdef
    have hφ : Function.Injective φ := S.subtype_injective.comp (e.symm.trans eS.symm).injective
    have hφS : φ.range = S := by
      rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (e.symm.trans eS.symm).surjective,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hφe : ∀ g : ↥S, φ (e (chevQuotHom 3 S g)) = g := fun g => by
      change ((eS.symm (e.symm (e (chevQuotHom 3 S g))) : ↥S) : Ω) = g
      rw [MulEquiv.symm_apply_apply, show chevQuotHom 3 S g = eS g from rfl,
        MulEquiv.symm_apply_apply]
    have hφΓ : ∀ b x, φ (Γ b x) = b * φ x * b⁻¹ := fun b x => by
      obtain ⟨g, rfl⟩ : ∃ g : ↥S, e (chevQuotHom 3 S g) = x :=
        ⟨eS.symm (e.symm x), by
          rw [show chevQuotHom 3 S (eS.symm (e.symm x)) = eS (eS.symm (e.symm x)) from rfl,
            MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩
      rw [hΓe, hφe, hφe]
    by_cases hout : ∃ b ∈ B, Γ b ∉ I
    · obtain ⟨b, hb, hbI⟩ := hout
      exact TwE6Outer.concA_of_twistedE6_three_of_not_mem_inndiag hK hf hℓ2 h3 hS hcore hZ hB hBC
        h7 hφ hφS hb hbI (hφΓ b)
    · push Not at hout
      exact ModelGen.concA_of_modelAGen Nat.prime_three (by norm_num) hS hcore hZ hB hBC
        (h6' hout) φ hφ hφS (TwE6Outer.modelAGen_twistedE6_three_of_dvd_add_one hK hf hℓ2 h3)
  ·
    by_cases hout : ∃ b ∈ B, Γ b ∉ I
    · obtain ⟨b, hb, hbI⟩ := hout
      exact hc2 hZ h7 b hb hbI
    · push Not at hout
      exact hc1 hZ (h6' hout)

end Split

section Head

open CFSG.LieType.SeitzGeneration

theorem concA_badExcCore_twistedE6_three_of_mod_two_of_inputs (hVtw : TwE6VtwInput)
    (hJc : TwE6JCompInput)
    (hR1 : ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {Ω : Type}
      [Group Ω] [Finite Ω] {S B : Subgroup Ω}, TwE6VtwInput → TwE6JCompInput →
      Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 → ∀ (hS : S.Normal),
      ⁅S, S⁆ = S → GLAPPrimeCore 3 ↥S = ⊥ → IsElemAbelian 3 B →
      Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3 → 3 ^ 4 ≤ Nat.card B →
      ∀ (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
        {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))},
        (∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
          e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)) →
        Γ.ker = centModSubgroup 3 S →
        B.map Γ ≤ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
          twistedE6Diag K (unitaryInvolution K ℓ f) →
        3 ^ 6 ≤ Nat.card ↥(B.map Γ) → S267ConcA 3 S B)
    (hR2 : ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {Ω : Type}
      [Group Ω] [Finite Ω] {S B : Subgroup Ω}, TwE6VtwInput → TwE6JCompInput →
      Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 → ∀ (hS : S.Normal),
      ⁅S, S⁆ = S → GLAPPrimeCore 3 ↥S = ⊥ → IsElemAbelian 3 B →
      Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3 → 3 ^ 4 ≤ Nat.card B →
      ∀ (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
        {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))},
        (∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
          e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)) →
        Γ.ker = centModSubgroup 3 S → ∀ {b : Ω}, b ∈ B →
        Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
          twistedE6Diag K (unitaryInvolution K ℓ f) →
        3 ^ 6 ≤ Nat.card ↥(B.map Γ ⊓ (twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
          twistedE6Diag K (unitaryInvolution K ℓ f))) → S267ConcA 3 S B)
    (hc1 : ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ],
      Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 →
      ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S →
        GLAPPrimeCore 3 ↥S = ⊥ → Subgroup.center ↥S ≠ ⊥ →
        (PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))) →
        Nat.card B ≤ 3 ^ 6 → S267ConcA 3 S B)
    (hc2 : ∀ {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ],
      Nat.card K = (ℓ ^ f) ^ 2 → 1 ≤ f → ℓ ≠ 2 → 3 ∣ ℓ ^ f + 1 →
      ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} (hS : S.Normal), ⁅S, S⁆ = S →
        GLAPPrimeCore 3 ↥S = ⊥ → Subgroup.center ↥S ≠ ⊥ → IsElemAbelian 3 B →
        Nat.card B ≤ 3 ^ 7 →
        ∀ (e : PSimple 3 S ≃* ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f)))
          {Γ : Ω →* MulAut ↥(twistedE6RootGroup K (unitaryInvolution K ℓ f))},
          (∀ (b : Ω) (g : ↥S), Γ b (e (chevQuotHom 3 S g)) =
            e (chevQuotHom 3 S ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)) →
          ∀ {b : Ω}, b ∈ B →
          Γ b ∉ twistedE6Inn K (unitaryInvolution K ℓ f) ⊔
            twistedE6Diag K (unitaryInvolution K ℓ f) →
          S267ConcA 3 S B)
    {p q : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (_hq : q.Prime) (hq2 : q ≠ 2) (_hqp : q ≠ p)
    {Ω : Type} [Group Ω] [Finite Ω] (_hK : CFSG.Open.IsKGroup Ω) {S B : Subgroup Ω}
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (_hSB : S ⊔ B = ⊤) (_hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B)
    (hB4 : p ^ 4 ≤ Nat.card B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (_hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4)) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group)
    (_hd : p ∣ Q.card ^ 2 - 1) (hp3 : p = 3) (h1 : 3 ∣ Q.card + 1)
    (_hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  subst hp3
  rw [TauCeti.LieTypeIndex.characteristic_twistedE6] at hchar
  subst hchar
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  obtain ⟨K, _, σ, hKc, hσ, ⟨ec⟩⟩ := exists_catEquiv_twistedE6 Q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKc]
    exact pow_ne_zero 2 (pow_ne_zero _ Q.prime_p.ne_zero))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K Q.p := charP_of_card_eq_prime_pow (f := Q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hKc, ← pow_mul])
  have hσ' : σ = unitaryInvolution K Q.p Q.exponent :=
    RingEquiv.ext fun c => (hσ c).trans (unitaryInvolution_apply K Q.p Q.exponent c).symm
  subst hσ'
  have h3 : 3 ∣ Q.p ^ Q.exponent + 1 := by rwa [← TauCeti.PrimePower.card_def]
  set e₀ := e.trans ec with he₀
  obtain ⟨Γ, hΓ, hΓker⟩ := ModelGen.exists_actHom_pSimple hS hperf e₀
  refine Or.inl (concA_twistedE6_three_of_pSimple hKc Q.exponent_pos hq2 h3 hS hcore hB hBC e₀ hΓ
    hΓker (fun hI h6 => ?_) (fun b hb hbI h6 => ?_) (fun hZ hBle => ?_)
    (fun hZ hBle b hb hbI => ?_))
  · exact hR1 hVtw hJc hKc Q.exponent_pos hq2 h3 hS hperf hcore hB hBC hB4 e₀ hΓ hΓker hI h6
  · exact hR2 hVtw hJc hKc Q.exponent_pos hq2 h3 hS hperf hcore hB hBC hB4 e₀ hΓ hΓker hb hbI h6
  · exact hc1 hKc Q.exponent_pos hq2 h3 hS hperf hcore hZ e₀ hBle
  · exact hc2 hKc Q.exponent_pos hq2 h3 hS hperf hcore hZ hB hBle e₀ hΓ hb hbI

theorem concA_badExcCore_twistedE6_three_of_mod_two :
    ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
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
      S267ConcA p S B ∨ S267ConcBCDE p q S B :=
  concA_badExcCore_twistedE6_three_of_mod_two_of_inputs TwE6Vtw.twE6VtwInput_holds
    twE6JCompInput_holds concA_of_twE6_vtw_image concA_of_twE6_vtw_outer
    TwE6Central.concA_twistedE6_three_of_center_ne_bot_of_card_le
    TwE6Central.concA_twistedE6_three_of_center_ne_bot_of_not_mem_inndiag

end Head

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
