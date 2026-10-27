module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConcB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldModelA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}


theorem concA_badExcCore_F4_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.F4 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.F4 Q, hv⟩).Group) (hdvd : p ∣ Q.card ^ 2 - 1) :
    S267ConcA p S B := by
  have hle : Nat.card B ≤ p ^ (Tag.F4.rank + 2) := by
    obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.f4 Q hv
    haveI := hKc
    have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
    exact card_le_pow_rank_add_two_F4 hp hS hperf hB hBC hK (eC.symm.trans e.symm)
      fun F hF => card_le_pow_rank_F4_of_dvd_sq hp hp2 hpK hF
  rcases card_le_or_eq_of_le hp hB hle with hle | heq
  · exact concA_badExcCore_F4_of_inner hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd hle
  · exact concA_badExcCore_F4_of_outer hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd heq

theorem concA_badExcCore_E6_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hdvd : p ∣ Q.card ^ 2 - 1)
    (hp3 : p ≠ 3) :
    S267ConcA p S B := by
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨Θ, hΘ⟩ := CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_hom_ringAut_E (Or.inl rfl) K
    hp hp5
  by_cases h1 : p ∣ Q.card - 1
  · have hpK : p ∣ Nat.card K - 1 := by rwa [hK]
    have hle : Nat.card B ≤ p ^ (Tag.E6.rank + 2) :=
      card_le_pow_add_two_of_hom hp hS hperf hB hBC (eC.symm.trans e.symm)
        center_adjointGroup_eq_bot Θ hΘ (card_le_pow_rank_E6_of_dvd_sub_one hp hp5 hpK)
    rcases card_le_or_eq_of_le hp hB hle with hle | heq
    · exact concA_badExcCore_E6_of_dvd_sub_one_of_card_le hp hq2 hS hperf hcore hB hBC hv hchar e
        hp5 h1 hle
    · exact concA_badExcCore_E6_of_dvd_sub_one_of_card_eq hp hq2 hS hperf hcore hB hBC hv hchar e
        hp5 h1 heq
  · have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
    have hpK1 : ¬ p ∣ Nat.card K - 1 := by rwa [hK]
    have hle : Nat.card B ≤ p ^ (frameSize .E6 + 2) :=
      card_le_pow_add_two_of_hom hp hS hperf hB hBC (eC.symm.trans e.symm)
        center_adjointGroup_eq_bot Θ hΘ fun F hF => card_le_pow_four_E6_of_dvd_sq hp hp5 hpK hpK1 hF
    rcases card_le_or_eq_of_le hp hB hle with hle | heq
    · exact concA_badExcCore_E6_of_inner hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd h1 hle
    · exact concA_badExcCore_E6_of_outer hp hq2 hS hperf hcore hB hBC hv hchar e hp5 hdvd h1 heq

theorem concA_badExcCore_E7_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E7 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E7 Q, hv⟩).Group) (hdvd : p ∣ Q.card ^ 2 - 1) :
    S267ConcA p S B := by
  have hle : Nat.card B ≤ p ^ (Tag.E7.rank + 2) := by
    obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 Q hv
    have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
    exact card_le_pow_rank_add_two_E78 (Or.inl rfl) hp hp2 hS hperf hB hBC hpK (eC.symm.trans e.symm)
  rcases card_le_or_eq_of_le hp hB hle with hle | heq
  · exact concA_badExcCore_E7_of_inner hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd hle
  · exact concA_badExcCore_E7_of_outer hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd heq

theorem concA_badExcCore_E8_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E8 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E8 Q, hv⟩).Group) (hdvd : p ∣ Q.card ^ 2 - 1) :
    S267ConcA p S B := by
  have hle : Nat.card B ≤ p ^ (Tag.E8.rank + 2) := by
    obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 Q hv
    have hpK : p ∣ Nat.card K ^ 2 - 1 := by rwa [hK]
    exact card_le_pow_rank_add_two_E78 (Or.inr rfl) hp hp2 hS hperf hB hBC hpK (eC.symm.trans e.symm)
  rcases card_le_or_eq_of_le hp hB hle with hle | heq
  · exact concA_badExcCore_E8_of_inner hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd hle
  · exact concA_badExcCore_E8_of_outer hp hq2 hS hperf hcore hB hBC hv hchar e hp2 hdvd heq

theorem badExcCore_dvd_of_twistedE6_of_three
    (h2E6 : ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {p q : ℕ}, p.Prime → p ≠ 2 →
      q ≠ 2 → S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ → IsElemAbelian p B →
      Nat.card ↥(B ⊓ centModSubgroup p S) = p →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid),
        (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) →
        p ∣ Q.card ^ 2 - 1 → p ≠ 3 → S267ConcA p S B)
    (hE6one : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid),
        (TauCeti.LieTypeIndex.E6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) → p ∣ Q.card ^ 2 - 1 →
        p = 3 → p ∣ Q.card - 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B)
    (hE6two : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid),
        (TauCeti.LieTypeIndex.E6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) → p ∣ Q.card ^ 2 - 1 →
        p = 3 → ¬ p ∣ Q.card - 1 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B)
    (h2E6three : ∀ {p q : ℕ}, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      ∀ {Ω : Type} [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω →
      ∀ {S B : Subgroup Ω}, S.Normal → ⁅S, S⁆ = S → GLAPPrimeCore p ↥S = ⊥ →
        IsElemAbelian p B → S ⊔ B = ⊤ → p ^ GLATwoLocalRank p Ω ≤ Nat.card B →
        p ^ 4 ≤ Nat.card B → Nat.card ↥(B ⊓ centModSubgroup p S) = p →
        ¬ (p = 3 ∧ Nat.card B = 3 ^ 4) →
      ∀ {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid),
        (TauCeti.LieTypeIndex.twistedE6 Q).characteristic = q →
        (PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedE6 Q, hv⟩).Group) →
        p ∣ Q.card ^ 2 - 1 → p = 3 →
        (∃ (K' : Type) (_ : Group K') (_ : Finite K'),
          Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
            GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) →
        S267ConcA p S B ∨ S267ConcBCDE p q S B) :
    ∀ (mk : TauCeti.PrimePower → TauCeti.LieTypeIndex),
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
        S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  intro mk hmk p q hp hp2 hq hq2 hqp Ω _ _ hK S B hS hperf hcore hB hSB hrank hB4 hBC hp3B Q hv
    hchar e hd hHq
  rcases hmk with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (concA_badExcCore_F4_of_dvd hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hd)
  · by_cases hp3 : p = 3
    · by_cases h1 : p ∣ Q.card - 1
      · exact hE6one hp hp2 hq hq2 hqp hK hS hperf hcore hB hSB hrank hB4 hBC hp3B hv hchar e hd
          hp3 h1 hHq
      · exact hE6two hp hp2 hq hq2 hqp hK hS hperf hcore hB hSB hrank hB4 hBC hp3B hv hchar e hd
          hp3 h1 hHq
    · exact Or.inl (concA_badExcCore_E6_of_dvd hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hd hp3)
  · by_cases hp3 : p = 3
    · exact h2E6three hp hp2 hq hq2 hqp hK hS hperf hcore hB hSB hrank hB4 hBC hp3B hv hchar e hd
        hp3 hHq
    · exact Or.inl (h2E6 hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hd hp3)
  · exact Or.inl (concA_badExcCore_E7_of_dvd hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hd)
  · exact Or.inl (concA_badExcCore_E8_of_dvd hp hp2 hq2 hS hperf hcore hB hBC hv hchar e hd)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
