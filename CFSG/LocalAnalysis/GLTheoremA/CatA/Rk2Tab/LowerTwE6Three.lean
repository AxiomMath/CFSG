module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLiftLocal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwE6
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedLevi
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedCent
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
open CFSG.LieType.Chevalley.E6GraphLevi
open scoped MatrixGroups Pointwise


theorem rk2_low_twe6_three (K : Type) [Group K] [Finite K] (lab : GLALabel)
    (hK : Rk2IsLabel K lab) (htag : lab.tag = .twE6) (hn : lab.n = 3) :
    5 ≤ CFSG.Open.evenRank K := by
  classical
  have hleK : CFSG.Open.twoLocalPrimeRank 3 K ≤ CFSG.Open.evenRank K := by
    have h := CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_le_evenRank
      3 Nat.prime_three (by norm_num) K
    simpa only [CFSG.RankThreeEvenClassification.Helpers.twoLocalRank] using h
  by_cases hc : Subgroup.center K = ⊥
  ·
    obtain ⟨F, hField, hFin, σ, hcard, hσ, ⟨eK⟩⟩ :=
      exists_twistedE6RootGroup_of_isLabel hK htag hc
    letI : Field F := hField
    letI : Finite F := hFin
    have hF : Nat.card F = (2 ^ 3) ^ 2 := by rw [hcard, hn]
    have hσ' : ∀ c, σ c = c ^ (2 ^ 3) := by rw [← hn]; exact hσ
    have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank 3 ↥(twistedE6RootGroup F σ) := by
      haveI : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (k := 3 * 2) (by norm_num) (by rw [hF, pow_mul])
      obtain ⟨σ₀, hσ₀, -, hσ₀2, S, hSmem, hScard⟩ :=
        CFSG.LinearGroups.finite_field_quadratic_frobenius (K := F) Nat.prime_two
          (by norm_num) hF
      set L : Subgroup (ModGL TwistTag.E6.tag F) :=
        subsystemGroup TwistTag.E6.tag F setA ⊓
          graphFixedRootGroup TwistTag.E6 F σ.toRingHom with hLdef
      have hfacts := subsystemGroup_inf_facts (k := ↥S) (K := F) (f := 3) (by norm_num)
        hScard hF (σ := σ.toRingHom) hσ'
      have hZ : Subgroup.center ↥L = ⊥ := hfacts.2.2.1
      have hq : CFSG.Open.IsQuasisimple ↥L := hfacts.2.2.2
      obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -,
        -, -, hmodel, -⟩⟩ :=
        even_E6_graph_finite_Levi_intersections (f := 3) (by norm_num) ↥S F hScard hF
          σ.toRingHom hσ'
      have hS' : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 3 := by
        have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
          (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
        exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel
      have hT : LieOddRankChev := uc22p20x_lieOddRankChev
        CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
      have hpr : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 5 := by
        rw [uc22p20w_pRank_psu hT hq hS' Nat.prime_three (by norm_num)]
        rw [hZ]
        simp only [Subgroup.card_bot]
        have hpow : (2 : ℕ) ^ 3 = 8 := by norm_num
        rw [hpow]
        unfold rkLin
        simp only [Bool.false_eq_true, if_false, if_true]
        have he : eM 8 3 = 1 := uc22p20v_eM_of_dvd (n := 3) (p := 3) (by norm_num)
        rw [he]
        have h9 : padicValNat 3 (8 + 1) = 2 := by
          rw [show (8 + 1 : ℕ) = 3 ^ 2 by norm_num]
          exact padicValNat.prime_pow (p := 3) 2
        have h6 : padicValNat 3 6 = 1 := by
          rw [show (6 : ℕ) = 3 * 2 by norm_num]
          rw [padicValNat.mul (by norm_num) (by norm_num),
            padicValNat.self (by norm_num : 1 < 3),
            padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
        have hcond : ¬ (¬ 3 ∣ 1 ∧ 3 ∣ 6 ∧ 4 ≤ 6 ∧
            padicValNat 3 (8 + 1) ≤ padicValNat 3 6) := by
          rintro ⟨-, -, -, hle⟩
          rw [h9, h6] at hle
          omega
        rw [if_neg hcond]
        norm_num
      obtain ⟨E, hEle, hEel, hEcard⟩ :=
        CFSG.RankThreeEvenClassification.Helpers.pRank_attained 3 Nat.prime_three
          (⊤ : Subgroup ↥L)
      have hEcard5 : Nat.card E = 3 ^ 5 := by rw [hEcard, hpr]
      let J : Set (Fin TwistTag.E6.foldedTag.rank) := foldedSetA
      let Q : Subgroup (ModGL TwistTag.E6.tag F) :=
        graphFixedParabolicRadical TwistTag.E6 F σ.toRingHom J
      obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLleP, -, -, -, -, -, hQp, hQne⟩ :=
        diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 F σ J
      have hQC : Q ≤ twistedE6RootGroup F σ :=
        graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 F σ.toRingHom J
      have hLC0 : L ≤ twistedE6RootGroup F σ := inf_le_right
      have hLlevi : L ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J := by
        show L ≤ parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion J) ⊓
          graphFixedRootGroup TwistTag.E6 F σ.toRingHom
        rw [show TwistTag.E6.orbitUnion J = setA from orbitUnion_foldedSetA]
        exact inf_le_inf (subsystemGroup_le_parabolicLevi' (E := F)) le_rfl
      have hPnorm : graphFixedParabolic TwistTag.E6 F σ.toRingHom J ≤
          Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag F)) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).mp hQnorm
      have hLnorm : L ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag F)) :=
        (hLlevi.trans hLleP).trans hPnorm
      let X : Subgroup ↥(twistedE6RootGroup F σ) := Q.subgroupOf (twistedE6RootGroup F σ)
      have hJne : J ≠ Set.univ := by
        have hrank : TwistTag.E6.foldedTag.rank = 4 := by decide
        intro hJ
        have hmem : (Fin.cast hrank.symm (3 : Fin 4)) ∈ foldedSetA := by
          have h1 : (Fin.cast hrank.symm (3 : Fin 4)) ∈
              (Set.univ : Set (Fin TwistTag.E6.foldedTag.rank)) := Set.mem_univ _
          rwa [← hJ] at h1
        simp [foldedSetA] at hmem
      have hXne : X ≠ ⊥ := by
        intro h
        apply hQne hJne
        rw [eq_bot_iff]
        intro x hx
        have hx' : (⟨x, hQC hx⟩ : ↥(twistedE6RootGroup F σ)) ∈ X := by
          rw [Subgroup.mem_subgroupOf]
          exact hx
        rw [h] at hx'
        have hx1 : (⟨x, hQC hx⟩ : ↥(twistedE6RootGroup F σ)) = 1 :=
          Subgroup.mem_bot.mp hx'
        exact congrArg Subtype.val hx1
      have hX2 : IsPGroup 2 X :=
        (hQp 2).of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
      let E' : Subgroup ↥(twistedE6RootGroup F σ) := E.map (Subgroup.inclusion hLC0)
      have hE'el : CFSG.Open.IsElemAbelian 3 E' :=
        CFSG.SectionRank.isElemAbelian_map hEel _
      have hE'card : Nat.card E' = 3 ^ 5 := by
        rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hLC0), hEcard5]
      have hE'le : E' ≤ Subgroup.normalizer (X : Set ↥(twistedE6RootGroup F σ)) := by
        have h1 : E' ≤ (Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag F))).subgroupOf
            (twistedE6RootGroup F σ) := by
          intro x hx
          obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
          exact hLnorm e.2
        rwa [Subgroup.subgroupOf_normalizer_eq hQC] at h1
      exact le_twoLocalPrimeRank_of_normalizer Nat.prime_three hXne hX2 hE'el hE'card hE'le
    have hcongr : CFSG.Open.twoLocalPrimeRank 3 K =
        CFSG.Open.twoLocalPrimeRank 3 ↥(twistedE6RootGroup F σ) := by
      have h := CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr
        (p := 3) (by norm_num) eK
      exact h.symm
    rw [hcongr] at hleK
    exact h5.trans hleK
  ·
    have h5 : 5 ≤ CFSG.Open.twoLocalPrimeRank 3 K :=
      rk2_split_low_twE6_cover hK Nat.prime_three (by norm_num) htag (by omega)
        (by rw [hn]; norm_num) hc
    exact h5.trans hleK

end CFSG.LocalAnalysis.GLTheoremA
