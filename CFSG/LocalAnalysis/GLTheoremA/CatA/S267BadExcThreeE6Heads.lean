module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Out
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldModelA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcThreeE6Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


@[expose] def OuterOfDiagInput : Prop :=
  ∀ {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} {τ : Tag},
    (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
    ∀ {K : Type} [Field K] [Finite K], ringChar K ≠ 2 → ∀ {p : ℕ}, p.Prime → p ≠ 2 →
    (τ = .E6 → p ≠ 3 ∨ ¬ p ∣ Nat.card K - 1) → p ∣ Nat.card K ^ 2 - 1 → S.Normal →
    GLAPPrimeCore p ↥S = ⊥ → Subgroup.center ↥S = ⊥ → IsElemAbelian p B →
    Nat.card ↥(B ⊓ centModSubgroup p S) = p → Nat.card B = p ^ (frameSize τ + 2) →
    (↥(adjointGroup τ K) ≃* PSimple p S) →
    (∀ F : Subgroup ↥(adjointGroup τ K), IsElemAbelian p F → Nat.card F ≤ p ^ frameSize τ) →
    S267ConcA p S B

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem card_le_three_pow_six_E6_of_mod_two (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K % 3 = 2) (eX : ↥(adjointGroup .E6 K) ≃* PSimple 3 S) :
    Nat.card B ≤ 3 ^ (4 + 2) := by
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  obtain ⟨Θ, hΘ⟩ := exists_hom_ringAut_E6_three K (by omega)
  exact card_le_pow_add_two_of_hom Nat.prime_three hS hperf hB hBC eX center_adjointGroup_eq_bot Θ
    hΘ fun F hF => card_le_pow_four_E6_three_of_mod_two hK hF

theorem concA_badExcCore_E6_three_of_mod_two_of_outer (houter : OuterOfDiagInput) {p q : ℕ}
    (hp : p.Prime) (hq2 : q ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp3 : p = 3)
    (h3 : 3 ∣ Q.card + 1) : S267ConcA p S B := by
  subst hp3
  have hmod : Q.card % 3 = 2 := by omega
  have hdvd1 : ¬ 3 ∣ Q.card - 1 := by omega
  have hdvd : 3 ∣ Q.card ^ 2 - 1 := by
    have h1 : Q.card ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hmod]
    have h2 : 1 ≤ Q.card ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hQp : Q.p = q := by rw [← hchar, TauCeti.LieTypeIndex.characteristic_E6]
  obtain ⟨K, _, _, hK, hKc, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p, hQp]; exact hq2
  have hKm : Nat.card K % 3 = 2 := by rw [hK]; exact hmod
  have hK1 : ¬ 3 ∣ Nat.card K - 1 := by omega
  have hKsq : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact hdvd
  set eX : ↥(adjointGroup .E6 K) ≃* PSimple 3 S := eC.symm.trans e.symm with heX
  rcases card_le_or_eq_of_le Nat.prime_three hB
      (card_le_three_pow_six_E6_of_mod_two hS hperf hB hBC hKm eX) with hle | heq
  · exact concA_badExcCore_E6_of_inner Nat.prime_three hq2 hS hperf hcore hB hBC hv hchar e
      (by norm_num) hdvd hdvd1 hle
  · have hK5 : 5 ≤ Nat.card K :=
      five_le_card_of_dvd_sq_sub_one hK2 Nat.prime_three (by norm_num) hKsq
    have hZ : Subgroup.center ↥S = ⊥ := center_eq_bot_of_adjointGroup Nat.prime_three hperf hcore
      eX (by
        obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.e6_hopfMultiplier hK5
        rw [Nat.card_congr eM.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
        exact fun h => hK1 (h.trans (Nat.gcd_dvd_right 3 _)))
    exact houter (Or.inr (Or.inl rfl)) hK2 Nat.prime_three (by norm_num) (fun _ => Or.inr hK1)
      hKsq hS hcore hZ hB hBC heq eX fun F hF => card_le_pow_four_E6_three_of_mod_two hKm hF

theorem outerOfDiagInput_holds : OuterOfDiagInput := by
  intro Ω _ _ S B τ hτ K _ _ hK2 p hp hp2 hdiag hpQ hS hcore hZ hB hBC hBc eX hX
  exact concA_of_adjointGroup_of_outer_of_diag hτ hK2 hp hp2 hdiag hpQ hS hcore hZ hB hBC hBc eX hX

theorem concA_badExcCore_E6_three_of_mod_two {p q : ℕ} (hp : p.Prime) (hq2 : q ≠ 2)
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hp3 : p = 3)
    (h3 : 3 ∣ Q.card + 1) : S267ConcA p S B :=
  concA_badExcCore_E6_three_of_mod_two_of_outer outerOfDiagInput_holds hp hq2 hS hperf hcore hB
    hBC hv hchar e hp3 h3

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
