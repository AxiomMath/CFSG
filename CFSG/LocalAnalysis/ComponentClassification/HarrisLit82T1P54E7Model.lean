module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54E7Theta
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Defs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFourPresentation
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg.CentralExt CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model

variable {p f : ℕ} [Fact p.Prime]

theorem card_center_E7sc (hp2 : p ≠ 2) (hf : f ≠ 0) : Nat.card (center (E7sc p f)) = 2 := by
  rw [(MinusculeClosed.card_center_e7 (GaloisField p f)).1, GaloisField.card p f hf]
  obtain ⟨k, hk⟩ := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow (n := f)
  rw [hk, Nat.add_sub_cancel]
  exact Nat.gcd_eq_left (dvd_mul_right 2 k)

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem concl_E7sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : M₇} (ht : t ∈ center M₇)
    (ht2 : orderOf t = 2) : P54.Concl p f M₇ t := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  obtain ⟨-, hRθF, hperf⟩ := e7_fund_class hp2 hq
  obtain ⟨u, hu, hu2⟩ := exists_involution_std hp2 hq isRoot_thetaE7
  have hQ7 : IsQuasisimple M₇ := isQuasisimple_e7 (GaloisField p f)
  have hZ7 : IsPGroup 2 (center M₇) :=
    IsPGroup.of_card (n := 1) (by rw [card_center_E7sc hp2 hf, pow_one])
  have hO7 := pPrimeCore_eq_bot_of_quasisimple hQ7 hZ7 hu2
  obtain ⟨e⟩ := nonempty_theta_equiv hp2 hq
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf]
    omega
  have hQ1 : IsQuasisimple ↥(stdRankOne D₇ thetaE7) :=
    LocalCores.isQuasisimple_of_mulEquiv e.symm
      (LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)
  have hZ1 : IsPGroup 2 (center ↥(stdRankOne D₇ thetaE7)) := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (LieType.HighestRoot.mul_self_eq_one_of_mem_center e g.2)⟩
  have hu2' : orderOf (⟨u, hu⟩ : ↥(stdRankOne D₇ thetaE7)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu2
  have hO1 := pPrimeCore_eq_bot_of_quasisimple hQ1 hZ1 hu2'
  obtain ⟨hQ2, hZ2, hL2⟩ := hj_facts hp2 hq
  have htJ : t ∈ HJ p f := center_le_HJ ht
  have ht2' : orderOf (⟨t, htJ⟩ : ↥(HJ p f)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact ht2
  have hO2 := pPrimeCore_eq_bot_of_quasisimple hQ2 hZ2 ht2'
  have hn1 : ∀ g ∈ centralizer {u}, ∀ j ∈ stdRankOne D₇ thetaE7,
      g * j * g⁻¹ ∈ stdRankOne D₇ thetaE7 := by
    intro g hg j hj
    rw [← conjSub_theta hp2 hq hu hu2 (Subgroup.mem_centralizer_singleton_iff.1 hg)]
    exact conj_mem_conjSub hj
  have hn2 : ∀ g ∈ centralizer {u}, ∀ j ∈ HJ p f, g * j * g⁻¹ ∈ HJ p f := fun g hg j hj =>
    conjSub_HJ_le hp2 hq hu hu2 (Subgroup.mem_centralizer_singleton_iff.1 hg) (conj_mem_conjSub hj)
  refine ⟨u, hu2, ?_, stdRankOne D₇ thetaE7, HJ p f,
    isTwoComponentIn_of_normalizes (theta_le_centralizer hp2 hq hu hu2) hn1
      (isTwoQuasisimple_of_quasisimple hQ1 hZ1 hu2'),
    isTwoComponentIn_of_normalizes (HJ_le_centralizer hp2 hq hu) hn2
      (isTwoQuasisimple_of_quasisimple hQ2 hZ2 ht2'), ?_, hu, ?_, ⟨.POmegaPlus, 6, ?_⟩,
    Or.inl htJ⟩
  · rw [fusionZStar_eq_center_of_pPrimeCore_eq_bot hO7]
    intro hc
    rw [no_central_fund hp2 hq hRθF hu hc, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  · intro h
    have hC := commutes_HJ_theta hp2 hq
    rw [← h] at hC
    have hab : ⁅stdRankOne D₇ thetaE7, stdRankOne D₇ thetaE7⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx =>
        Subgroup.mem_centralizer_iff.2 fun y hy => hC y hy x hx
    rw [hperf _ hRθF] at hab
    have hu1 : u = 1 := by
      rw [← Subgroup.mem_bot, ← hab]
      exact hu
    rw [hu1, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  · refine ⟨GaloisField p f, inferInstance, Fintype.ofFinite _, ?_,
      ⟨(quotientPPrimeCoreEquiv hO1).trans e⟩⟩
    rw [Fintype.card_eq_nat_card, GaloisField.card p f hf]
  · exact lieModel_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center_of_pPrimeCore_eq_bot hO2).symm)
      hL2

end CFSG.ComponentClassification.HarrisLit.T1.P54.E7Row
