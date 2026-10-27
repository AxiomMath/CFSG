module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Criteria
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Parts
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.TwoFive
public import CFSG.Sporadic.HNOddCore.InvRow4b
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Blueprint CFSG.Sporadic.HNSchreier CFSG.HardMathSupport.Solomon.LocalBalance

set_option maxRecDepth 20000 in
theorem sporadicOuterHolds_HN_three
    : SporadicOuterHolds .HN 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.HN := e
  have e' : S ≃* JH := e0.trans hnEquivJ
  refine noOuterFixesCentralizer_of_fixed_dvd (Nat.factorial 10) ?_ ?_
  · intro σ hσ2 hσ H hH
    have hσ1 : σ ≠ 1 := fun h => hσ (h ▸ (innerAut S).one_mem)
    have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
    obtain ⟨f⟩ := CFSG.Sporadic.HNOddCore.hn_outer_involution_fixSub e0 σ hord hσ
    have hle : H ≤ CFSG.Sporadic.Schreier.fixSub σ := fun x hx =>
      CFSG.Sporadic.Schreier.mem_fixSub.2 (hH x hx)
    have hdvd := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_congr f.toEquiv, Nat.card_perm, Nat.card_fin] at hdvd
  · intro s hs hdvd
    have hs' : orderOf (e' s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hs
    have hcard := @card_centralizer_mulEquiv S _ ↥JH inferInstance e' s
    rw [← hcard] at hdvd
    have h544 : Nat.card (CJ (sJ 0)) = 544320 := card_CJ_s1
    have h29160 : Nat.card (CJ (sJ 2)) = 29160 := card_CJ_s3
    rcases (order_three_classes (e' s)).1 hs' with h | h
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      rw [← hc, card_centralizer_conj, h544] at hdvd
      revert hdvd
      decide
    · obtain ⟨c, hc⟩ := isConj_iff.1 h
      rw [← hc, card_centralizer_conj, h29160] at hdvd
      revert hdvd
      decide

theorem gLAPPrimeCoreOf_CJ_s1
    : CFSG.Open.GLAPPrimeCoreOf 3 (CJ (sJ 0)) = ⊥ := by
  obtain ⟨hsup, -, hcomm⟩ := CJ_s1_structure
  have hsimple : IsSimpleGroup ↥(L1J) := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcardL : Nat.card ↥(L1J) = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  exact gLAPPrimeCoreOf_eq_bot_of_zpowers_sup_simple Nat.prime_three (orderOf_sJ (by norm_num))
    hsup hcomm commutator_CJ_s1 hsimple (by rw [hcardL]; norm_num)

open CFSG.Sporadic.HNOddCore (jR jR_injective t2J t4J involution_cover_R exists_J_conj
  not_isConj_c_jR t2_sqR t2_ne_oneR t4J_sq t4J_ne_one card_CJ_t2 card_CJ_t4)

theorem hn_card_centralizer_involution
    (x : JH) (hx : orderOf x = 2) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) = 177408000 ∨
      Nat.card ↥(Subgroup.centralizer ({x} : Set JH)) = 3686400 := by
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hy2 : (jR x) ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have hy1 : jR x ≠ 1 := fun h =>
    hx1 (jR_injective (h.trans (map_one _).symm))
  rcases involution_cover_R hy2 hy1 with h | h | h
  · exact absurd h (not_isConj_c_jR x)
  · obtain ⟨g, hg⟩ := exists_J_conj t2_sqR
      t2_ne_oneR h
    have hgx : g * t2J * g⁻¹ = x := jR_injective (by
      rw [map_mul, map_mul, map_inv]; exact hg)
    left
    rw [← hgx, card_centralizer_conj]
    exact card_CJ_t2
  · have h4sq : (jR t4J) ^ 2 = 1 := by
      rw [← map_pow, pow_two, t4J_sq, map_one]
    have h41 : jR t4J ≠ 1 := fun h' =>
      t4J_ne_one
        (jR_injective (h'.trans (map_one _).symm))
    obtain ⟨g, hg⟩ := exists_J_conj h4sq h41 h
    have hgx : g * t4J * g⁻¹ = x := jR_injective (by
      rw [map_mul, map_mul, map_inv]; exact hg)
    right
    rw [← hgx, card_centralizer_conj]
    exact card_CJ_t4

@[expose] def HNThreeWitness
    : Prop :=
  ∃ u g : JH, u ∈ CJ (sJ 2) ∧ orderOf u = 5 ∧ g ∈ CJ (sJ 2) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u

theorem gLAPPrimeCoreOf_CJ_s3_of_witness
    (hw : HNThreeWitness) : CFSG.Open.GLAPPrimeCoreOf 3 (CJ (sJ 2)) = ⊥ := by
  obtain ⟨u, g, hu, hu5, hg, hgu⟩ := hw
  have hC : Nat.card (CJ (sJ 2)) = 3 ^ 6 * 40 := by rw [card_CJ_s3]; norm_num
  refine gLAPPrimeCoreOf_eq_bot_of_card_forty (a := 6) (by norm_num) hC ?_
    (not_normal_five_of_witness hC hu hu5 hg hgu)
  intro w hw2 Q hQ hle
  have hdvd := Subgroup.card_dvd_of_le hle
  have hlt : 9 < 3 ^ (6 - 1) := by norm_num
  rcases hn_card_centralizer_involution w hw2 with h | h <;> rw [h] at hdvd <;>
  · have := card_le_of_isPGroup_of_dvd Nat.prime_three hQ (e := 2) (by norm_num) hdvd
    omega

theorem sporadicOPrimeHolds_HN_three_of_witness
    (hw : HNThreeWitness) : SporadicOPrimeHolds .HN 3 := by
  intro S _ _ _ ⟨e⟩
  have e0 : S ≃* NativeSporadic.HN := e
  have e' : S ≃* JH := e0.trans hnEquivJ
  refine @OPrimeCoreTrivialAt.of_mulEquiv 3 S _ ↥JH inferInstance e' ?_
  intro y hy
  rcases (order_three_classes y).1 hy with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc]
    exact (gLAPPrimeCoreOf_centralizer_conj c _).2 gLAPPrimeCoreOf_CJ_s1
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc]
    exact (gLAPPrimeCoreOf_centralizer_conj c _).2 (gLAPPrimeCoreOf_CJ_s3_of_witness hw)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
