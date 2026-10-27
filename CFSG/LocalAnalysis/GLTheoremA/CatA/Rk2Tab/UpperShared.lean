module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTL4Mult
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotUniqueBasic
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Multiplier CFSG.Assembly

theorem twoLocalPrimeRank_le_of_card_le {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (h : ∀ R E : Subgroup K, R ≠ ⊥ → IsPGroup 2 R →
      E ≤ Subgroup.normalizer (R : Set K) → IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    CFSG.Open.twoLocalPrimeRank p K ≤ k := by
  refine csSup_le' ?_
  rintro a ⟨H, hH, rfl⟩
  obtain ⟨R, hR, hR2, rfl⟩ := hH
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEel => h R E hR hR2 hE hEel

theorem glaTwoLocalRank_le_of_card_le {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (h : ∀ R E : Subgroup K, R ≠ ⊥ → IsPGroup 2 R →
      E ≤ Subgroup.normalizer (R : Set K) → IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    GLATwoLocalRank p K ≤ k :=
  twoLocalPrimeRank_le_of_card_le hp h

private lemma card_generic_exceptional_psp (n f : ℕ) (hf : 2 ≤ f) :
    Nat.card (Multiplier.generic .PSp n 2 f × Multiplier.exceptional .PSp n 2 f) = 1 := by
  have hodd : Nat.gcd 2 (2 ^ f - 1) = 1 := CFSG.SeitzReduction.SymplecticPilot.gcd_two_two_pow_sub_one (by omega)
  have hex : Multiplier.exceptionalOrders .PSp n 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders, hodd, hex,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma card_generic_exceptional_psl (f : ℕ) (hf : 2 ≤ f) :
    Nat.card (Multiplier.generic .PSL 4 2 f × Multiplier.exceptional .PSL 4 2 f) = 1 := by
  have hodd : Nat.gcd 4 (2 ^ f - 1) = 1 := CFSG.EvenSporadicStandard.HSStd.PumpT.gcd_four_two_pow_sub_one (by omega)
  have hex : Multiplier.exceptionalOrders .PSL 4 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders, hodd, hex,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma card_generic_exceptional_pomegaPlus (n f : ℕ) (hf : 2 ≤ f) :
    Nat.card (Multiplier.generic .POmegaPlus n 2 f ×
      Multiplier.exceptional .POmegaPlus n 2 f) = 1 := by
  have hev : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hex : Multiplier.exceptionalOrders .POmegaPlus n 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders, hev, hex,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma card_generic_exceptional_f4 (f : ℕ) (hf : 2 ≤ f) :
    Nat.card (Multiplier.generic .F4 0 2 f × Multiplier.exceptional .F4 0 2 f) = 1 := by
  have hex : Multiplier.exceptionalOrders .F4 0 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders, hex,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma card_generic_exceptional_e7 (f : ℕ) (hf : 2 ≤ f) :
    Nat.card (Multiplier.generic .E7 0 2 f × Multiplier.exceptional .E7 0 2 f) = 1 := by
  have hodd : Nat.gcd 2 (2 ^ f - 1) = 1 := CFSG.SeitzReduction.SymplecticPilot.gcd_two_two_pow_sub_one (by omega)
  have hex : Multiplier.exceptionalOrders .E7 0 2 f = (1, 1) := by
    unfold Multiplier.exceptionalOrders
    split <;> simp_all
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders, hodd, hex,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

private lemma card_generic_exceptional_e8 (f : ℕ) :
    Nat.card (Multiplier.generic .E8 0 2 f × Multiplier.exceptional .E8 0 2 f) = 1 := by
  simp [Multiplier.generic, Multiplier.exceptional, Multiplier.genericOrders,
    Multiplier.exceptionalOrders, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

private lemma subsingleton_multiplier_of_row {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hrow : CFSG.LieType.Steinberg.CentralExt.GriessAll.GriessRow X t n p f)
    (h : Nat.card (Multiplier.generic t n p f × Multiplier.exceptional t n p f) = 1) :
    Subsingleton (CFSG.Open.griessHopfMultiplier X) := by
  obtain ⟨-, ⟨e⟩⟩ := hrow
  refine (Nat.card_eq_one_iff_unique.mp ?_).1
  rw [Nat.card_congr e.toEquiv, h]

theorem rk2_center_eq_bot_of_large {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hn : 2 ≤ lab.n) : Subgroup.center K = ⊥ := by
  classical
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.2 hQ
  refine CFSG.GH74.GLS.Stage2.Signalizer.Odd87.center_eq_bot_of_hopf_subsingleton hQ'
    (MulEquiv.refl _) ?_
  obtain ⟨t, l, n⟩ := lab
  rcases ht with ht | ht | ht | ht | ht
  · subst ht
    have hM' : LieModel (K ⧸ Subgroup.center K) .PSp l 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hn' : 2 ≤ n := hn
    have hq : 5 ≤ 2 ^ n ∨ 2 ^ n = 4 ∨ (2 ^ n = 2 ∧ 4 ≤ l) ∨ (2 ^ n = 3 ∧ 3 ≤ l) := by
      rcases eq_or_lt_of_le hn' with h | h
      · right; left; rw [← h]; norm_num
      · left
        calc 5 ≤ 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have hrow := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_row
      (hM'.statedClassicalModel (by decide)) hq
    exact subsingleton_multiplier_of_row hrow (card_generic_exceptional_psp l n (by omega))
  · subst ht
    by_cases hr : l = 3
    · have hM' : LieModel (K ⧸ Subgroup.center K) .PSL 4 2 n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hr] using hM
      have hrow := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row
        (hM'.statedClassicalModel (by decide))
      exact subsingleton_multiplier_of_row hrow (card_generic_exceptional_psl n (by omega))
    · have hM' : LieModel (K ⧸ Subgroup.center K) .POmegaPlus l 2 n := by
        simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
          CFSG.StandardType.markRank, CFSG.StandardType.markChar,
          CFSG.StandardType.markDeg, hr] using hM
      have hq : 3 ≤ 2 ^ n ∨ (2 ^ n = 2 ∧ 5 ≤ l) := by
        left
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have hrow := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row
        (hM'.statedClassicalModel (by decide)) hq
      exact subsingleton_multiplier_of_row hrow
        (card_generic_exceptional_pomegaPlus l n (by omega))
  · subst ht
    have hM' : LieModel (K ⧸ Subgroup.center K) .F4 0 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hq : 3 ≤ 2 ^ n := by
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hrow := CFSG.LieType.Steinberg.CentralExt.GriessNative.f4_row
      (hM'.chevalleyExceptionalModel (by decide)) hq
    exact subsingleton_multiplier_of_row hrow (card_generic_exceptional_f4 n (by omega))
  · subst ht
    have hM' : LieModel (K ⧸ Subgroup.center K) .E7 0 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hrow := CFSG.LieType.Steinberg.CentralExt.GriessNative.e7_row
      (hM'.chevalleyExceptionalModel (by decide))
    exact subsingleton_multiplier_of_row hrow (card_generic_exceptional_e7 n (by omega))
  · subst ht
    have hM' : LieModel (K ⧸ Subgroup.center K) .E8 0 2 n := by
      simpa [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hrow := CFSG.LieType.Steinberg.CentralExt.GriessNative.e8_row
      (hM'.chevalleyExceptionalModel (by decide))
    exact subsingleton_multiplier_of_row hrow (card_generic_exceptional_e8 n)

end CFSG.LocalAnalysis.GLTheoremA
