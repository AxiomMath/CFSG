module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevSigma
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.GroupTheory.WeirSylow.Symplectic
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
import CFSG.RankThree.PartOne.KF.ClsOmega
import CFSG.LargeExtraspecial.DWFldLinear
import CFSG.Open.StatedAPI
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LargeExtraspecial.Types
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.GroupTheory.ClassTwoThree
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.Timmesfeld.Outcome
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace RankChevProof

open CFSG.Open CFSG.SectionRank CFSG.GroupTheory.WeirSylow CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.Multiplier CFSG.Models

theorem sp_rank_arith (e l : ℕ) :
    (if Even e then 2 * l else l) / e = l / (e / Nat.gcd e 2) := by
  by_cases he : Even e
  · obtain ⟨k, hk⟩ := he
    have h2 : Nat.gcd e 2 = 2 := Nat.gcd_eq_right ⟨k, by omega⟩
    rw [if_pos ⟨k, hk⟩, h2, show e = 2 * k by omega, Nat.mul_div_mul_left _ _ two_pos,
      Nat.mul_div_cancel_left _ two_pos]
  · have hodd : Odd e := Nat.not_even_iff_odd.1 he
    have h1 : Nat.gcd e 2 = 1 := Nat.coprime_two_right.2 hodd
    rw [if_neg he, h1, Nat.div_one]

theorem not_dvd_of_dvd_two_pow {r z k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hz : z ∣ 2 ^ k) :
    ¬ r ∣ z := fun h =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow (h.trans hz)))

theorem pRank_statedSp {p : ℕ} [hp : Fact p.Prime] (hp1 : Odd p) (K : Type) [Field K] [Fintype K]
    (hpK : ¬ p ∣ Fintype.card K) (n : ℕ) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSp n K)) =
      (if Even (orderOf (Fintype.card K : ZMod p)) then 2 * n else n) /
        orderOf (Fintype.card K : ZMod p) :=
  pRank_eq_of_sylow_sigmaModel p (one_le_weirA hpK) fun P => sylow_Sp hp1 K hpK n P

end RankChevProof

open RankChevProof CFSG.Open CFSG.Blueprint.Multiplier in
theorem pRank_chev_B (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) {l : ℕ} {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B l Q).Valid) (hQ : Q.p = 2)
    (e : (K ⧸ Subgroup.center K) ≃* TauCeti.ValidLieTypeIndex.Group ⟨.B l Q, hv⟩)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    CFSG.Open.pRank r (⊤ : Subgroup K) = rkSp l Q.card r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hl2 : 2 ≤ l :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff (.B l Q)).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
  have hm : CFSG.Open.StatedClassicalModel (K ⧸ Subgroup.center K) .PSp l Q.p Q.exponent := by
    rcases Nat.eq_or_lt_of_le hl2 with h2 | h3
    · subst h2
      exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 Q hv e
    · exact CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even l Q hv hQ h3 e
  have hLM : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .PSp l Q.p Q.exponent :=
    ⟨hm.1, Or.inl hm⟩
  have hdvd := ksm_card_center_dvd hG hq hLM
  have hgen : genericOrders .PSp l Q.p Q.exponent =
      (Nat.gcd 2 (Q.p ^ Q.exponent - 1), 1) := rfl
  have hexc : ∃ k, (exceptionalOrders .PSp l Q.p Q.exponent).1 *
      (exceptionalOrders .PSp l Q.p Q.exponent).2 = 2 ^ k := by
    unfold exceptionalOrders
    split <;> first | exact ⟨1, rfl⟩ | exact ⟨0, rfl⟩ | simp_all
  obtain ⟨k, hk⟩ := hexc
  have hg1 : Nat.gcd 2 (Q.p ^ Q.exponent - 1) = 1 := by
    rw [hQ]
    have h2 : 2 ∣ 2 ^ Q.exponent := dvd_pow_self 2 Q.exponent_pos.ne'
    have hpos : 1 ≤ 2 ^ Q.exponent := Nat.one_le_two_pow
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun h => ?_
    have h1 : 2 ∣ 2 ^ Q.exponent - (2 ^ Q.exponent - 1) := Nat.dvd_sub h2 h
    have h3 : 2 ^ Q.exponent - (2 ^ Q.exponent - 1) = 1 := by omega
    rw [h3] at h1
    exact absurd h1 (by norm_num)
  rw [hgen, hk, hg1] at hdvd
  have hrZ : ¬ r ∣ Nat.card (Subgroup.center K) :=
    not_dvd_of_dvd_two_pow hr hr2 (k := k) (by simpa using hdvd)
  obtain ⟨-, K', instF, instFin, hcard, ⟨φ⟩⟩ := hm
  haveI : Fintype K' := Fintype.ofFinite K'
  have hKc : Fintype.card K' = 2 ^ Q.exponent := by
    rw [Fintype.card_eq_nat_card, hcard, hQ]
  haveI : CharP K' 2 := CFSG.LargeExtraspecial.DW.charP_two_of_card_eq (f := Q.exponent)
    (by rw [hcard, hQ])
  have hpK : ¬ r ∣ Fintype.card K' := by
    rw [hKc]
    exact not_dvd_of_dvd_two_pow hr hr2 (dvd_refl _)
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := l) (K := K')
  let ψ : ↥(StatedSp l K') ≃* StatedProj (StatedSp l K') :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot
  rw [← CFSG.SectionRank.pRank_quotient_eq (Subgroup.center K) hrZ,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt (φ.trans ψ.symm),
    pRank_statedSp (hr.odd_of_ne_two hr2) K' hpK l, hKc]
  have hQc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  unfold rkSp eS
  rw [hQc, orderOf_pow' _ two_ne_zero, sp_rank_arith]

end CFSG.LocalAnalysis.RankThreeUC.S15
