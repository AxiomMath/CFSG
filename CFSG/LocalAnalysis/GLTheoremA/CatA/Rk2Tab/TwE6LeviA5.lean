module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwE6LeviRank
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedLevi
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Torus
public import CFSG.RankThree.PartOne.S15K.FamilyBlock
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcE6TwistedCent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
  CFSG.ComponentClassification.RankTwoExceptional.TwistedE6Sec8
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.RankThreeUC.S15


private theorem rkLin_six_false_le_five {Q p z : ℕ} (hem : eM Q p = 1) :
    rkLin 6 false Q p z ≤ 5 := by
  unfold rkLin
  simp only [Bool.false_eq_true, if_false]
  rw [if_pos hem]
  split_ifs <;> omega

theorem card_le_pow_five_of_le_graphFixedParabolicLevi_A5 {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = (2 ^ n) ^ 2) (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1)
    {E : Subgroup (ModGL TwistTag.E6.tag F)}
    (hE : E ≤ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5)
    (hEel : CFSG.Open.IsElemAbelian p E) :
    Nat.card E ≤ p ^ 5 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hF
      norm_num at hF
      have h2 : 1 < Nat.card F := Finite.one_lt_card (α := F)
      omega
    · exact h
  let k := CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.fixedSubfield σ.toRingHom
  have hk : Nat.card k = 2 ^ n :=
    CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_fixedSubfield_of_card
      (k := F) σ.toRingHom hF hσ
  let L : Subgroup (ModGL TwistTag.E6.tag F) :=
    subsystemGroup TwistTag.E6.tag F setA ⊓ graphFixedRootGroup TwistTag.E6 F σ.toRingHom
  let T : Subgroup (ModGL TwistTag.E6.tag F) := thetaTorus (algebraMap (↥k) F)
  obtain ⟨-, htw⟩ := CFSG.LieType.Chevalley.even_E6_graph_finite_Levi_intersections
    (f := n) hn (k := ↥k) (K := F) hk hF σ.toRingHom hσ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hinf, hcomm, huniq, hinj0, -, -, -, -, -, -, -, -, -,
    -, -, -, hmodel, -, -, -, -, -, -⟩ := htw
  obtain ⟨-, -, hZ, hqsim⟩ :=
    subsystemGroup_inf_facts (k := ↥k) (K := F) (f := n) hn hk hF (σ := σ.toRingHom) hσ
  have hinj : Function.Injective
      ((thetaTorusHom F).comp (Units.map (algebraMap (↥k) F).toMonoidHom)) := by
    intro a b h
    exact hinj0 (by simpa only [MonoidHom.comp_apply, thetaTorusHom_apply] using h)
  have hcardT : Nat.card T = Nat.card (↥k)ˣ :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hpt : ¬ p ∣ Nat.card T := by
    rw [hcardT, Nat.card_units, hk]
    exact CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one
      (Nat.one_le_pow n 2 (by norm_num)) (by have := hp.two_le; omega) hpq
  have hEsub : E ≤ L := by
    intro e he
    have hE0 : e ∈ parabolicLevi TwistTag.E6.tag F setA ⊓
        graphFixedRootGroup TwistTag.E6 F σ.toRingHom := by
      have h : e ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom twE6MaxA5 := hE he
      rwa [graphFixedParabolicLevi, show TwistTag.E6.orbitUnion twE6MaxA5 = setA from
        orbitUnion_foldedSetA] at h
    obtain ⟨⟨l, t⟩, ⟨hl, ht, heq⟩, -⟩ := huniq e hE0
    have hcom : Commute l t := hcomm l hl t ht
    have hep : (l * t) ^ p = 1 := by
      rw [← heq]
      exact hEel.2 e he
    rw [hcom.mul_pow] at hep
    have htp : t ^ p = 1 := by
      have h1 : t ^ p = (l ^ p)⁻¹ := eq_inv_of_mul_eq_one_right hep
      have hmem : l ^ p ∈ L ⊓ T := by
        refine ⟨L.pow_mem hl p, ?_⟩
        have h3 : (t ^ p)⁻¹ ∈ T := T.inv_mem (T.pow_mem ht p)
        rwa [h1, inv_inv] at h3
      rw [hinf] at hmem
      rw [h1, Subgroup.mem_bot.1 hmem, inv_one]
    have ht1 : t = 1 := by
      have hdvd : orderOf t ∣ p := orderOf_dvd_iff_pow_eq_one.mpr htp
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exfalso
        have hdvdT : orderOf (⟨t, ht⟩ : ↥T) ∣ Nat.card T := orderOf_dvd_natCard _
        rw [← Subgroup.orderOf_coe (⟨t, ht⟩ : ↥T)] at hdvdT
        exact hpt (h ▸ hdvdT)
    rw [heq, ht1, mul_one]
    exact hl
  have hT : LieOddRankChev :=
    uc22p20x_lieOddRankChev CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hS' : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 n := by
    have e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel
  have hpr : CFSG.Open.pRank p (⊤ : Subgroup ↥L) = rkLin 6 false (2 ^ n) p
      (Nat.card (Subgroup.center ↥L)) :=
    uc22p20w_pRank_psu hT hqsim hS' hp hp2
  have hpr5 : CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 5 := by
    rw [hpr, hZ, Subgroup.card_bot]
    exact rkLin_six_false_le_five (eM_eq_one_iff.2 hpq)
  let E' : Subgroup ↥L := E.subgroupOf L
  have hE'el : CFSG.Open.IsElemAbelian p E' :=
    CFSG.Open.IsElemAbelian.comap hEel L.subtype_injective
  have hcardE' : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsub).toEquiv
  obtain ⟨m, hm⟩ := (hE'el.isPGroup).exists_card_eq
  have hm5 : m ≤ 5 := by
    have h1 : m ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
      CFSG.SectionRank.le_pRank hp.one_lt le_top hE'el hm
    exact h1.trans hpr5
  rw [← hcardE', hm]
  exact Nat.pow_le_pow_right hp.pos hm5

end CFSG.LocalAnalysis.GLTheoremA
