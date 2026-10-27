module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.PCore.FixedSubgroupCore
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
public import CFSG.RankThree.PartOne.KE.SuzukiFinal
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs
public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open
open CFSG.Blueprint (suzukiGroup)
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Dickson.SuzukiReeB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private theorem pPrimeCore_five_suzukiGroup_zero
    {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    CFSG.pPrimeCore 5 (suzukiGroup 0 k) = ⊥ := by
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro R hR hcop
  obtain ⟨P, -, -, -, hcore⟩ :=
    (CFSG.LieType.Ree.suzuki_two_normal_five_complement_core_trivial hk).2
  exact hcore R hR hcop.symm

theorem oddCoreFact_five_suzukiGroup_two {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    OddCoreFact 5 (suzukiGroup 2 K) := by
  have hZ : Subgroup.center (suzukiGroup 2 K) = ⊥ :=
    suzuki_center_eq_bot (by norm_num) hK
  constructor
  ·
    have hdvd := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd
      (a := 2) (by norm_num) hK).2
    have hodd : Odd (Nat.card (Outer (suzukiGroup 2 K))) := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h <;> rw [h] <;> norm_num
    exact CFSG.Quasithin.H13.OutTwoNilp.outTwoNilpotent_of_twoNilpotent_outer
      (CFSG.Quasithin.H13.OutTwoNilp.twoNilpotent_of_odd hodd)
  · intro α hα
    have hα5 : α ^ 5 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    have hα1 : α ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hα
      norm_num at hα
    rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 5 α]
    change Odd (Nat.card (GLAPPrimeCoreOf 5 (fixSubgroup α)))
    by_cases hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup 2 K)
    ·
      obtain ⟨x, rfl, hx5, hx1⟩ :=
        exists_eq_conj_of_mem_range hZ hin hα5 hα1
      rw [fixSubgroup_conj]
      have hxord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
      have hxodd : Odd (orderOf x) := by rw [hxord]; norm_num
      exact odd_card_gLAPPrimeCoreOf_of_odd_card 5
        ((CFSG.RankThree.Suzuki_involution_centralizers_and_inner_odd_centralizers
          (a := 2) (by norm_num) hK).2 x hx1 hxodd).1
    ·
      obtain ⟨σ, h, b, k, _, _, -, hb, hk, hconj, ⟨efix⟩⟩ :=
        suzukiPrimeFieldCosetDescent 2 (by norm_num) K hK 5 Nat.prime_five (by norm_num) α hα hin
      have hb0 : b = 0 := by omega
      subst hb0
      have hk2 : Nat.card k = 2 := by rw [hk]; norm_num
      have hbot0 : CFSG.pPrimeCore 5 (suzukiGroup 0 k) = ⊥ :=
        pPrimeCore_five_suzukiGroup_zero hk2
      have hbotField : CFSG.pPrimeCore 5 ↥(fixSubgroup (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut 2 K σ)) = ⊥ :=
        pPrimeCore_eq_bot_of_mulEquiv 5 efix.symm hbot0
      have hcongr : MulAut.congr (MulAut.conj h : suzukiGroup 2 K ≃* suzukiGroup 2 K) α =
          CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut 2 K σ := hconj
      have hbotα : CFSG.pPrimeCore 5 ↥(fixSubgroup α) = ⊥ := by
        have h1 : CFSG.pPrimeCore 5
            ↥(fixSubgroup (MulAut.congr (MulAut.conj h) α)) = ⊥ := by
          rw [hcongr]
          exact hbotField
        exact pPrimeCore_eq_bot_of_mulEquiv 5
          (fixSubgroupCongrEquiv (MulAut.conj h) α).symm h1
      rw [gLAPPrimeCoreOf_eq_bot_iff_pPrimeCore.mpr hbotα, Subgroup.card_bot]
      exact odd_one

theorem oddCoreFact_five_of_suzuki_two {S : Type} [Group S]
    [Finite S] (hv : (TauCeti.LieTypeIndex.suzuki 2).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group) :
    OddCoreFact 5 S := by
  obtain ⟨-, a, ha, K, _, _, hf, hK', ⟨θ⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
  have ha2 : a = 2 := by omega
  subst ha2
  exact (oddCoreFact_congr (p := 5) (e.trans θ)).mpr
    (oddCoreFact_five_suzukiGroup_two hK')

end CFSG.LocalAnalysis.GLTheoremA.KD1912
