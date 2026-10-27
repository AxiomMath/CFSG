module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.StepSeven
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CoreTwoL34
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxGrp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.QuotientCentralizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_outer_quotient_pCore {K : Subgroup G}
    (hL : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2))) :
    Group.IsSolvable (Outer (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  haveI : Group.IsSolvable (Outer (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
      3 (GaloisField 2 2))) :=
    CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux.isSolvable_out_projectiveSL
      (K := GaloisField 2 2) (by norm_num)
  obtain ⟨e⟩ := hL
  exact solvable_of_equiv (G := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
      3 (GaloisField 2 2)) (H := ↥K ⧸ CFSG.pCore 2 ↥K)
    ((e.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3
      (GaloisField 2 2))).symm)

private theorem center_quotient_pCore_eq_bot
    {K : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hL : Nonempty (↥K ⧸ CFSG.pPrimeCore 3 ↥K ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2)))
    (hZ : Nat.card (Subgroup.center (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) = 1) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  have hpc : CFSG.pCore 2 ↥K = CFSG.pPrimeCore 3 ↥K :=
    pCore_two_eq_pPrimeCore_three hq hL
  have hZbot : Subgroup.center (↥K ⧸ CFSG.pPrimeCore 3 ↥K) = ⊥ :=
    Subgroup.card_eq_one.mp hZ
  have e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
    QuotientGroup.quotientMulEquivOfEq hpc
  rw [← center_map_equiv e.symm, hZbot, Subgroup.map_bot]

theorem kSubLeKSubAt_of
    {M : Subgroup G} (h3 : ∀ H ∈ H2StarAll M, CaseThree M H) (hTwo : KTwoComponentAt M)
    (hK : KNormalAt M) : KSubLeKSubAt M := by
  intro E H N h hEK hN hKN
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := kSub 3 M H
  let L : Subgroup G := kSub 3 M N
  let Q : Subgroup ↥L := CFSG.pCore 2 ↥L
  let hN' : HypCGen G M 3 E N := { h with mem := hN }
  have hLN : L ≤ N := kSub_le 3 M N
  have hKN' : K ≤ N := hKN
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := hK 3 E N hN'
  have hC3H : CaseThree M H := h3 H h.mem_H2StarAll
  have hC3N : CaseThree M N := h3 N hN'.mem_H2StarAll
  have hKperf : Group.IsPerfect ↥K :=
    HypCGen.isPerfect_kSub (M := M) (E := E) (H := H) hC3H
  have hqK : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    h.isQuasisimple_kSub_quotient hTwo
  have hqL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    hN'.isQuasisimple_kSub_quotient hTwo
  have hcenterK : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_quotient_pCore_eq_bot hqK (HypCGen.nonempty_mulEquiv_threeStar hC3H) hC3H.2.2
  have hcenterL : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ :=
    center_quotient_pCore_eq_bot hqL (HypCGen.nonempty_mulEquiv_threeStar hC3N) hC3N.2.2
  have hOutL : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
      CFSG.PGLModel.projSL 3 (GaloisField 2 2)) :=
    hN'.nonempty_mulEquiv_kSub_quotient_pCore_two hC3N hTwo
  have hOutSol : Group.IsSolvable (Outer (↥L ⧸ Q)) := by
    simpa [Q] using isSolvable_outer_quotient_pCore (K := L) hOutL
  have hXinfL : quotientCentralizer N L Q hLN hNL ⊓ L ≤ Q.map L.subtype := by
    simpa [Q] using quotientCentralizer_inf_le (Q := CFSG.pCore 2 ↥L) hLN hNL hcenterL
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    change ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L)
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)
  by_contra hKL
  have hKinfL : K ⊓ L ≤ CFSG.Open.pCoreOf 2 K :=
    inf_le_pCoreOf_of_quasisimple hKN' hNL hKperf hqK hcenterK hKL
  have hEinfL : E ⊓ L = ⊥ := by
    have hle : E ⊓ L ≤ E ⊓ CFSG.Open.pCoreOf 2 K :=
      le_inf inf_le_left ((le_inf (inf_le_left.trans hEK) inf_le_right).trans hKinfL)
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
  have hKsup : K ≤ L ⊔ quotientCentralizer N L Q hLN hNL :=
    perfect_le_sup_quotientCentralizer Q hLN hNL hKN' hKperf hOutSol
  have hEsup : E ≤ L ⊔ quotientCentralizer N L Q hLN hNL := hEK.trans hKsup
  obtain ⟨F, hFX, hFelem, hFcard⟩ :=
    exists_elemAbelian_nine_le_quotientCentralizer Q hLN hNL h.elem (by rw [h.card]; norm_num)
      hEsup hEinfL hXinfL hQ3
  obtain ⟨B, hB⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  have hBelem : CFSG.Open.IsElemAbelian 3 B :=
    isElemAbelian_of_isSylowOf (HypCGen.nonempty_mulEquiv_threeStar hC3N) hB
  have hBcard : Nat.card B = 9 :=
    card_eq_nine_of_isSylowOf (HypCGen.nonempty_mulEquiv_threeStar hC3N) hB
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 N :=
    four_le_pRank_of_quotientCentralizer Q hLN hNL hFX hFelem hFcard hB.le hBelem hBcard
      hXinfL hQ3
  have hNloc : IsTwoLocal N := (h.isMaxTwoLocal_of_mem_H2StarFam hN).1
  have hrank3 : CFSG.Open.pRank 3 N ≤ 3 :=
    h.cstar.pRank_le_three_of_isTwoLocal Nat.prime_three (by norm_num) h.not_mem_sigmaA hNloc
  omega

theorem fourteenFifteenNormAt_of
    {M : Subgroup G} (hpre : PreambleTypes M) (h3 : ∀ H ∈ H2StarAll M, CaseThree M H)
    (hTwo : KTwoComponentAt M) (hK : KNormalAt M) (hL : PLayerNotLeAt M) :
    FourteenFifteenNormAt M :=
  fourteenFifteenNormAt_of_kSubLe hpre h3 hTwo hK hL (kSubLeKSubAt_of h3 hTwo hK)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
