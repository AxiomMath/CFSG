module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseTwoSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.QuotientCentralizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxGrp
import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem S14Choice.pCoreOf_two_kSub_ne_bot_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hK : KNormalAt M) :
    CFSG.Open.pCoreOf 2 (kSub 3 M H) ≠ ⊥ :=
  h.hypCGen.pCoreOf_two_kSub_ne_bot_of_quasisimple h.J_comp.2.2.1
    (hK 3 E H h.hypCGen)

theorem S14Choice.normalizer_kSub_eq_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hK : KNormalAt M) :
    Subgroup.normalizer (kSub 3 M H : Set G) = H :=
  h.hypCGen.eq_normalizer_kSub_of_quasisimple h.J_comp.2.2.1 (hK 3 E H h.hypCGen)

theorem S14Choice.kSub_eq_of_le_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hL : PLayerNotLeAt M) {N : Subgroup G}
    (hN : IsMaxTwoLocalSubgroup N) (hKN : kSub 3 M H ≤ N) :
    kSub 3 M N = kSub 3 M H := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let A : Subgroup G := kSub 3 M N
  let QQ : Subgroup ↥A := CFSG.pPrimeCore 3 ↥A
  have hEnK : E ≤ K := h.E_le_kSub h2
  have hKnotM : ¬ K ≤ M := not_kSub_le_of_not_pLayerIn_le (hL 3 E H h.hypCGen)
  have hNstar : N ∈ H2StarFam M E :=
    h.hypCGen.mem_H2StarFam_of_isMaxTwoLocal hEnK hKnotM hN hKN
  have hNstarQ : N ∈ H2StarFam M Q :=
    mem_H2StarFam_of_le hNstar ((h.isSylowOf_kSub h2).le.trans hKN)
  have hN' : HypCGen G M 3 E N := { h.hypCGen with mem := hNstar }
  have hAN : A ≤ N := kSub_le 3 M N
  have hNA : N ≤ Subgroup.normalizer (A : Set G) := hK 3 E N hN'
  have hKperf : Group.IsPerfect ↥K := h2.1.isPerfect
  have hqK : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := h.J_comp.2.2.1
  have hpcK : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three_of_a11 hqK h2.2
  have hcenterK : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    have e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
      QuotientGroup.quotientMulEquivOfEq hpcK
    rw [← center_map_equiv e.symm, h2.2.center_eq_bot, Subgroup.map_bot]
  have hNall : N ∈ H2StarAll M := ⟨3, E, h.hypCGen.mem_QSet, hNstar⟩
  have hnoA : ¬ ∃ H' ∈ H2StarAll M, TypeA M H' :=
    fun ⟨H', hH', hAt⟩ => hA (h.prefA ⟨H', hH', hAt⟩)
  have hsingle : IsKComp M N A ∧ (IsL34Star A ∨ IsA11Star A) := by
    rcases (hpre 3 E h.hypCGen.mem_QSet N hNstar).2 with
      ⟨hcomp, h34 | hSL | hA11⟩ | htwo
    · exact ⟨hcomp, Or.inl h34⟩
    · exact absurd ⟨N, hNall, ⟨A, hcomp, hSL⟩⟩ hnoA
    · exact ⟨hcomp, Or.inr hA11⟩
    · obtain ⟨J₁, J₂, -, hJ₁, -, -, -, hSL₁, -⟩ := htwo
      exact absurd ⟨N, hNall, ⟨J₁, hJ₁, hSL₁⟩⟩ hnoA
  have hZ : Subgroup.center (threeStar A) = ⊥ := by
    rcases hsingle.2 with h34 | h11
    · exact Subgroup.card_eq_one.mp h34.2
    · exact h11.center_eq_bot
  have hOutA : Group.IsSolvable (Outer (↥A ⧸ QQ)) := by
    rcases hsingle.2 with h34 | h11
    · obtain ⟨e⟩ := nonempty_mulEquiv_projSL_of_isL34Type h34.1 h34.2
      haveI : Group.IsSolvable (Outer (projectiveSL 3 (GaloisField 2 2))) :=
        NormalizerAux.isSolvable_out_projectiveSL (K := GaloisField 2 2) (by norm_num)
      exact solvable_of_equiv (G := projectiveSL 3 (GaloisField 2 2))
        (H := threeStar A)
        ((e.trans (projSLEquivProjectiveSL 3 (GaloisField 2 2))).symm)
    · obtain ⟨e⟩ := h11
      haveI : Group.IsSolvable (Outer (alternatingGroup (Fin 11))) :=
        (CFSG.Quasithin.SteinbergCB.isSolvable_outer_alternatingGroup (n := 11)
          (Or.inr (by norm_num))).1
      exact solvable_of_equiv (G := alternatingGroup (Fin 11)) (H := threeStar A) e.symm
  have hXinfA : quotientCentralizer N A QQ hAN hNA ⊓ A ≤ QQ.map A.subtype :=
    quotientCentralizer_inf_le QQ hAN hNA hZ
  have hQ3 : ¬ 3 ∣ Nat.card QQ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hKA : K ≤ A := by
    by_contra hKL
    have hKinfA : K ⊓ A ≤ CFSG.Open.pCoreOf 2 K :=
      inf_le_pCoreOf_of_quasisimple hKN hNA hKperf hqK hcenterK hKL
    have hEinfA : E ⊓ A = ⊥ := by
      have hle : E ⊓ A ≤ E ⊓ CFSG.Open.pCoreOf 2 K :=
        le_inf inf_le_left ((le_inf (inf_le_left.trans hEnK) inf_le_right).trans hKinfA)
      have hcop : Nat.Coprime (Nat.card E) (Nat.card (CFSG.Open.pCoreOf 2 K)) := by
        rw [h.card]
        obtain ⟨m, hm⟩ :=
          (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K).exists_card_eq
        rw [hm]
        exact Nat.Coprime.pow_left 2 (Nat.Coprime.pow_right m
          ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num)))
      have hbot : E ⊓ CFSG.Open.pCoreOf 2 K = ⊥ :=
        (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
      exact le_bot_iff.mp (hle.trans (le_of_eq hbot))
    have hKsup : K ≤ A ⊔ quotientCentralizer N A QQ hAN hNA :=
      perfect_le_sup_quotientCentralizer QQ hAN hNA hKN hKperf hOutA
    have hEsup : E ≤ A ⊔ quotientCentralizer N A QQ hAN hNA := hEnK.trans hKsup
    obtain ⟨F, hFX, hFelem, hFcard⟩ :=
      exists_elemAbelian_nine_le_quotientCentralizer QQ hAN hNA h.elem
        h.card hEsup hEinfA hXinfA hQ3
    obtain ⟨B, hBA, hBelem, hBcard⟩ : ∃ B : Subgroup G,
        B ≤ A ∧ CFSG.Open.IsElemAbelian 3 B ∧ Nat.card B = 9 := by
      rcases hsingle.2 with h34 | h11
      · obtain ⟨e⟩ := nonempty_mulEquiv_projSL_of_isL34Type h34.1 h34.2
        obtain ⟨B, hB⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 A
        exact ⟨B, hB.le, isElemAbelian_of_isSylowOf ⟨e⟩ hB, card_eq_nine_of_isSylowOf ⟨e⟩ hB⟩
      · obtain ⟨F27, hF27A, hF27elem, hF27card⟩ := h11.exists_elemAbelian_le
        have hpRank : 2 ≤ CFSG.Open.pRank 3 F27 := by
          have h3 : 3 ≤ CFSG.Open.pRank 3 F27 :=
            CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hF27elem hF27card
          omega
        obtain ⟨B, hBF, hBelem, hBcard⟩ :=
          CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3) (k := 2) hpRank
        exact ⟨B, hBF.trans hF27A, hBelem, by rw [hBcard]; norm_num⟩
    have hrank4 : 4 ≤ CFSG.Open.pRank 3 N :=
      four_le_pRank_of_quotientCentralizer QQ hAN hNA hFX hFelem hFcard hBA hBelem hBcard
        hXinfA hQ3
    have hrank3 : CFSG.Open.pRank 3 N ≤ 3 :=
      h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num)
        h.hypCGen.not_mem_sigmaA hN.1
    omega
  have hAcalK : A ∈ calK M Q := by
    refine ⟨N, hNstarQ, hsingle.1, ?_⟩
    rcases hsingle.2 with h34 | h11
    · exact Or.inl h34.1
    · exact Or.inr h11
  exact h.J_star.2 A hAcalK hKA

theorem S14Choice.eq_of_isMaxTwoLocal_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hL : PLayerNotLeAt M) {N : Subgroup G}
    (hN : IsMaxTwoLocalSubgroup N) (hKN : kSub 3 M H ≤ N) : N = H := by
  have hEnK : E ≤ kSub 3 M H := h.E_le_kSub h2
  have hKnotM : ¬ kSub 3 M H ≤ M :=
    not_kSub_le_of_not_pLayerIn_le (hL 3 E H h.hypCGen)
  have hNstar : N ∈ H2StarFam M E :=
    h.hypCGen.mem_H2StarFam_of_isMaxTwoLocal hEnK hKnotM hN hKN
  have hN' : HypCGen G M 3 E N := { h.hypCGen with mem := hNstar }
  have hAeq : kSub 3 M N = kSub 3 M H :=
    h.kSub_eq_of_le_caseTwo hA h2 hpre hK hL hN hKN
  have hNnorm : N ≤ Subgroup.normalizer (kSub 3 M H : Set G) := by
    rw [← hAeq]
    exact hK 3 E N hN'
  have hNH : N ≤ H :=
    hNnorm.trans (h.normalizer_kSub_eq_caseTwo hK).le
  exact (hN.2 H h.hypCGen.isTwoLocal hNH).symm

theorem S14Choice.normalizer_le_caseTwo {M H E Q : Subgroup G}
    (h : S14Choice G M H E Q (kSub 3 M H)) (hA : ¬ TypeA M H) (h2 : CaseTwo M H)
    (hpre : PreambleTypes M) (hK : KNormalAt M) (hL : PLayerNotLeAt M) {C : Subgroup G}
    (hC2 : IsPGroup 2 C) (hC1 : C ≠ ⊥)
    (hKC : kSub 3 M H ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  have hloc : IsTwoLocal (Subgroup.normalizer (C : Set G)) := ⟨C, hC1, hC2, rfl⟩
  obtain ⟨N, hN, hNle⟩ :=
    CFSG.Quasithin.exists_maxTwoLocal_ge hloc
  have hKN : kSub 3 M H ≤ N := hKC.trans hNle
  have hNH : N = H := h.eq_of_isMaxTwoLocal_caseTwo hA h2 hpre hK hL hN hKN
  exact hNle.trans hNH.le

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
