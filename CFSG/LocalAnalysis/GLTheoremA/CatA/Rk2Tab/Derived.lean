module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankSmall
public import CFSG.Quasithin.Background.F918G2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallTits
public import CFSG.RankThree.PartOne.F106.QD32Exc
public import CFSG.LieType.Multipliers.Tits
public import CFSG.Models.Blueprint
public import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly
open CFSG.LieType.Ree

set_option linter.unusedSectionVars false


private theorem rk2Ord_one (p : ℕ) : rk2Ord p 1 = orderOf (2 : ZMod p) := by
  rw [rk2Ord, pow_one]

private theorem rk2Ord_thirteen : rk2Ord 13 1 = 12 := by
  rw [rk2Ord_one]
  have h : (2 : ZMod 13) ^ 12 = 1 := by decide
  have hd : orderOf (2 : ZMod 13) ∣ 12 := orderOf_dvd_of_pow_eq_one h
  have hle : orderOf (2 : ZMod 13) ≤ 12 := Nat.le_of_dvd (by norm_num) hd
  have h1 : (2 : ZMod 13) ^ 1 ≠ 1 := by decide
  have h2 : (2 : ZMod 13) ^ 2 ≠ 1 := by decide
  have h3 : (2 : ZMod 13) ^ 3 ≠ 1 := by decide
  have h4 : (2 : ZMod 13) ^ 4 ≠ 1 := by decide
  have h6 : (2 : ZMod 13) ^ 6 ≠ 1 := by decide
  have hnd1 : ¬ orderOf (2 : ZMod 13) ∣ 1 := fun hk =>
    h1 ((orderOf_dvd_iff_pow_eq_one).1 hk)
  have hnd2 : ¬ orderOf (2 : ZMod 13) ∣ 2 := fun hk =>
    h2 ((orderOf_dvd_iff_pow_eq_one).1 hk)
  have hnd3 : ¬ orderOf (2 : ZMod 13) ∣ 3 := fun hk =>
    h3 ((orderOf_dvd_iff_pow_eq_one).1 hk)
  have hnd4 : ¬ orderOf (2 : ZMod 13) ∣ 4 := fun hk =>
    h4 ((orderOf_dvd_iff_pow_eq_one).1 hk)
  have hnd6 : ¬ orderOf (2 : ZMod 13) ∣ 6 := fun hk =>
    h6 ((orderOf_dvd_iff_pow_eq_one).1 hk)
  interval_cases orderOf (2 : ZMod 13) <;> simp_all

private theorem rk2Mult_b2der_val (l n m : ℕ) :
    rk2Mult ⟨.B2der, l, n⟩ m = (if m % 2 = 0 then 4 / m else 2 / m) := rfl

private theorem rk2Mult_g2der_val (l n m : ℕ) :
    rk2Mult ⟨.G2der, l, n⟩ m = rk2Cnt [(2, true), (6, true)] m := rfl

private theorem rk2Mult_twF4der_val (l n m : ℕ) :
    rk2Mult ⟨.twF4der, l, n⟩ m = rk2Cnt [(1, true), (3, false), (4, true), (6, false)] m := rfl

private theorem rk2Mult_b2der_two {l : ℕ} : rk2Mult ⟨.B2der, l, 1⟩ 2 = 2 := by
  rw [rk2Mult_b2der_val]
  decide

private theorem rk2Mult_b2der_four {l : ℕ} : rk2Mult ⟨.B2der, l, 1⟩ 4 = 1 := by
  rw [rk2Mult_b2der_val]
  decide

private theorem six_div_le_rk2Mult_b2der {l p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    6 / p ≤ rk2Mult ⟨.B2der, l, 1⟩ (rk2Ord p 1) := by
  by_cases h3 : p = 3
  · subst h3
    rw [rk2Ord_three_one_eq_two, rk2Mult_b2der_two]
  by_cases h5 : p = 5
  · subst h5
    rw [rk2Ord_five_one_eq_four, rk2Mult_b2der_four]
  · have hp7 : 7 ≤ p := by
      rcases Nat.lt_or_ge p 7 with hlt | hge
      · interval_cases p <;> first
          | exact absurd rfl hp2
          | exact absurd rfl h3
          | exact absurd rfl h5
          | (norm_num [Nat.Prime] at hp)
      · exact hge
    rw [Nat.div_eq_of_lt (by omega : 6 < p)]
    exact Nat.zero_le _

private theorem rk2Mult_g2der_two {l : ℕ} : rk2Mult ⟨.G2der, l, 1⟩ 2 = 2 := by
  rw [rk2Mult_g2der_val]
  decide

private theorem rk2Mult_g2der_three {l : ℕ} : rk2Mult ⟨.G2der, l, 1⟩ 3 = 1 := by
  rw [rk2Mult_g2der_val]
  decide

private theorem rk2Mult_twF4der_two {l : ℕ} : rk2Mult ⟨.twF4der, l, 1⟩ 2 = 2 := by
  rw [rk2Mult_twF4der_val]
  decide

private theorem rk2Mult_twF4der_four {l : ℕ} : rk2Mult ⟨.twF4der, l, 1⟩ 4 = 2 := by
  rw [rk2Mult_twF4der_val]
  decide

private theorem rk2Mult_twF4der_twelve {l : ℕ} : rk2Mult ⟨.twF4der, l, 1⟩ 12 = 1 := by
  rw [rk2Mult_twF4der_val]
  decide

private theorem griessAllModels_statement : CFSG.Open.GriessAllModelsStatement :=
  CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

private theorem card_center_eq_one_of_griess_psu33 {K : Type} [Group K] [Finite K]
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 3 3 1) :
    Nat.card (Subgroup.center K) = 1 := by
  have hM' : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSU 3 3 1 :=
    CFSG.Models.LieModel.of_blueprint (by decide) hM
  have hdvd := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_card_center_dvd (K := K)
    griessAllModels_statement hQ hM'
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 3 1 = (1, 1) := by decide
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 3 1 = (1, 1) := by decide
  rw [hgen, hexc] at hdvd
  simpa using hdvd

private theorem card_center_eq_one_of_multiplier_tits {K : Type} [Group K] [Finite K]
    (hQ : CFSG.Open.IsQuasisimple K)
    (hM : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .Tits 0 2 1) :
    Nat.card (Subgroup.center K) = 1 := by
  have hQ' : CFSG.IsQuasisimple K :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Multipliers.Tits.multiplier_Tits
    (K ⧸ Subgroup.center K) hM
  have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) = 1 := by
    rw [Nat.card_congr eM.toEquiv]
    simp
  haveI : Finite (CFSG.Open.griessHopfMultiplier (K ⧸ Subgroup.center K)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf
    (L := K) (X := K ⧸ Subgroup.center K) hQ' (MulEquiv.refl _)
  rw [hcard] at hdvd
  simpa using hdvd

private theorem pRank_three_le_two_of_forall_card_lt {G : Type} [Group G] [Finite G]
    (h : ∀ E : Subgroup G, IsElemAbelian 3 E → Nat.card E < 3 ^ 3) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2 := by
  refine CFSG.SectionRank.pRank_le (p := 3) (k := 2) (by norm_num) fun E _ hE => ?_
  obtain ⟨k, hk⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.exists_card_eq_pow_of_isElemAbelian (G := G) (by norm_num) hE
  have hlt := h E hE
  rw [hk] at hlt ⊢
  have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hlt
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem pRank_three_commutator_reeFixed_F4_two_le {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥(commutator (reeFixed ReeTag.F4 K 0)))) ≤ 2 := by
  haveI : Finite (reeFixed ReeTag.F4 K 0) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.SectionRank.TitsOrder.Tits_card hK]
      norm_num)
  exact pRank_three_le_two_of_forall_card_lt fun E hE =>
    CFSG.StandardType.TableBExcSmallRest.card_lt_of_isElemAbelian_commutator_reeFixed hK hE

private theorem rk2_pRank_le_derived_of_markedModel {K : Type} [Group K] [Finite K]
    (lab : GLALabel) (p : ℕ) (hQ : CFSG.Open.IsQuasisimple K)
    (hlab : LargeEvenInLambda2 lab)
    (hM : CFSG.StandardType.MarkedModel lab (K ⧸ Subgroup.center K))
    (htag : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with rfl | rfl | rfl
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, rfl⟩ := hlab
    obtain ⟨e⟩ :=
      CFSG.StandardType.nonempty_alternatingGroup_of_markedModel_b2der rfl hM
    have h6 : CFSG.Open.pRank p (⊤ : Subgroup K) = 6 / p :=
      CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds (K := K) hQ 6 (by norm_num)
        ⟨e⟩ p hp hp2
    rw [h6]
    exact six_div_le_rk2Mult_b2der hp hp2
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, rfl⟩ := hlab
    have hMpsu : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 3 3 1 := by
      simpa only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hZ : Nat.card (Subgroup.center K) = 1 :=
      card_center_eq_one_of_griess_psu33 hQ hMpsu
    haveI : Fact p.Prime := ⟨hp⟩
    have hZ' : ¬ p ∣ Nat.card (Subgroup.center K) := by
      rw [hZ]
      intro hd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    have hqelim : CFSG.Open.pRank p (⊤ : Subgroup K) =
        CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
      (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ').symm
    rw [hqelim]
    have hcard : Nat.card (K ⧸ Subgroup.center K) = 6048 :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_g2der rfl hM
    by_cases hp3 : p = 3
    · subst hp3
      have hpsu : CFSG.Quasithin.IsPSU 3 3 1 (K ⧸ Subgroup.center K) :=
        hMpsu.statedClassicalModel (by decide)
      rw [CFSG.Quasithin.pRank_three_psu33 hpsu, rk2Ord_three_one_eq_two, rk2Mult_g2der_two]
    by_cases hp7 : p = 7
    · subst hp7
      have hle : CFSG.Open.pRank 7 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 1 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
          (p := 7) (k := 1) (by norm_num) (by rw [hcard]; norm_num)
      rw [rk2Ord_seven_one_eq_three, rk2Mult_g2der_three]
      exact hle
    · have hnot : ¬ p ∣ 6048 := by
        intro hd
        exact hp7 ((CFSG.LocalAnalysis.RankThreeUC.S15.RankSmall.prime_dvd_6048
          hp hp2 hp3).1.mp hd)
      have hle : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 0 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
          (p := p) (k := 0) hp.one_lt (by rw [hcard]; simpa using hnot)
      exact le_trans hle (Nat.zero_le _)
  ·
    simp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, rfl⟩ := hlab
    have hMtits : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .Tits 0 2 1 := by
      simpa only [CFSG.StandardType.MarkedModel, CFSG.StandardType.markTag,
        CFSG.StandardType.markRank, CFSG.StandardType.markChar,
        CFSG.StandardType.markDeg] using hM
    have hZ : Nat.card (Subgroup.center K) = 1 :=
      card_center_eq_one_of_multiplier_tits hQ hMtits
    haveI : Fact p.Prime := ⟨hp⟩
    have hZ' : ¬ p ∣ Nat.card (Subgroup.center K) := by
      rw [hZ]
      intro hd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    have hqelim : CFSG.Open.pRank p (⊤ : Subgroup K) =
        CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) :=
      (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hZ').symm
    rw [hqelim]
    have hcard : Nat.card (K ⧸ Subgroup.center K) = CFSG.Open.ordTits :=
      CFSG.LocalAnalysis.GLTheoremA.MI.card_markedModel_twF4der rfl hM
    by_cases hp3 : p = 3
    ·
      subst hp3
      have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 2 := by
        obtain ⟨K₀, _, _, _, hK₀, ⟨eC⟩⟩ :=
          CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model
            ((hMtits.reeTitsModel (by decide)).2)
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eC]
        exact pRank_three_commutator_reeFixed_F4_two_le hK₀
      rw [rk2Ord_three_one_eq_two, rk2Mult_twF4der_two]
      exact hle
    by_cases hp5 : p = 5
    · subst hp5
      have hle : CFSG.Open.pRank 5 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 2 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
          (p := 5) (k := 2) (by norm_num)
          (by rw [hcard]; norm_num [CFSG.Open.ordTits])
      rw [rk2Ord_five_one_eq_four, rk2Mult_twF4der_four]
      exact hle
    by_cases hp13 : p = 13
    · subst hp13
      have hle : CFSG.Open.pRank 13 (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 1 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
          (p := 13) (k := 1) (by norm_num)
          (by rw [hcard]; norm_num [CFSG.Open.ordTits])
      rw [rk2Ord_thirteen, rk2Mult_twF4der_twelve]
      exact hle
    · have hnot : ¬ p ∣ CFSG.Open.ordTits := by
        intro hd
        have hmem := CFSG.RankThree.PartOne.F106.prime_mem_of_dvd_tits hp
          (by simpa [CFSG.Open.ordTits] using hd)
        rcases hmem with rfl | rfl | rfl | rfl
        · exact hp2 rfl
        · exact hp3 rfl
        · exact hp5 rfl
        · exact hp13 rfl
      have hle : CFSG.Open.pRank p (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ 0 :=
        CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_top_le_of_not_dvd
          (p := p) (k := 0) hp.one_lt (by rw [hcard]; simpa using hnot)
      exact le_trans hle (Nat.zero_le _)

theorem rk2_pRank_le_derived {K : Type} [Group K] [Finite K] (lab : GLALabel) (p : ℕ)
    (hK : Rk2IsLabel K lab)
    (htag : lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨hQ, hlab, hM⟩ := rk2_model_of_isLabel hK
  exact rk2_pRank_le_derived_of_markedModel lab p hQ hlab hM htag hp hp2

end CFSG.LocalAnalysis.GLTheoremA
