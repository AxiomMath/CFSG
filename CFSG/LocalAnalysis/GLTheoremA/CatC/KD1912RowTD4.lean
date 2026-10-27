module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.HardMathSupport.Dickson.Bal207.Fam3D42LocalBal
public import CFSG.HardMathSupport.Dickson.Bal207.CoreFreeInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Group
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.Bal207 CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Quasithin.H13.OutTwoNilp

theorem pPrimeCore_centralizer_graphFixedRootGroup_triD4_two
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥d4P)
    (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hy : orderOf y = 3) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer
      ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) = ⊥ := by
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := inferInstance
  refine W2.core_eq_bot_of_noNormalPPrime Nat.prime_three ?_
  exact noNormalPPrime_centralizer_of_mulEquiv ψ
    (noNormalPPrime_centralizer_d4P (ψ y) (by rw [MulEquiv.orderOf_eq]; exact hy))

theorem pPrimeCore_fixSubgroup_graphFixedRootGroup_triD4_two_outer
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (x : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hx3 : x ^ 3 = 1)
    (hxout : x ∉ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    GLAPPrimeCoreOf 3 (fixSubgroup x) = ⊥ := by
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := inferInstance
  have h : NoNormalPPrime 3 (fixSub x) :=
    (coreFreeAt_three_D4_outer Nat.prime_two (by norm_num) le_rfl hK σ hσ x hx3 hxout).1
  exact W2.core_eq_bot_of_noNormalPPrime Nat.prime_three h

theorem outTwoNilpConcl_graphFixedRootGroup_triD4_two
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1)) :
    CFSG.LieType.ChevTwo.OutTwoNilpConcl
      ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, -, ⟨Θ, -, hΘsurj, hΘker, -⟩, -, hcardAut, -, -, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) le_rfl K hK σ hσ
  have hOut : Nat.card (Outer ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) = 3 := by
    have h1 : Nat.card (Outer ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) =
        Nat.card (K ≃+* K) := by
      have e' : Outer ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* (K ≃+* K) :=
        (QuotientGroup.quotientMulEquivOfEq hΘker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective (φ := Θ) hΘsurj)
      exact Nat.card_congr e'.toEquiv
    rw [h1, hcardAut]
  exact outTwoNilpotent_of_twoNilpotent_outer
    (twoNilpotent_of_odd (by rw [hOut]; norm_num))

theorem oddCoreFact_three_graphFixedRootGroup_two
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hK : Nat.card K = (2 ^ 1) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ 1))
    (ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥d4P) :
    OddCoreFact 3 ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  obtain ⟨-, -, ⟨Θ, -, hΘsurj, hΘker, -⟩, -, hcardAut, -, hZ, -⟩ :=
    even_triality_exact_automorphism_normal_form (f := 1) le_rfl K hK σ hσ
  refine ⟨outTwoNilpConcl_graphFixedRootGroup_triD4_two σ hK hσ, ?_⟩
  intro x hx
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  rw [odd_card_gLAPPrimeCoreOf_innerAut_inf_centralizer_iff hZ 3 x]
  change Odd (Nat.card (GLAPPrimeCoreOf 3 (fixSubgroup x)))
  by_cases hin : x ∈ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  · obtain ⟨y, rfl⟩ := hin
    have hy3 : orderOf y = 3 := by
      rw [← orderOf_injective (MulAut.conj :
        ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        (mulAutConj_injective_of_center_eq_bot hZ) y]
      exact hx
    have hfix : fixSubgroup (MulAut.conj y) = Subgroup.centralizer
        ({y} : Set ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :=
      fixSub_conj_eq_centralizer y
    rw [hfix, pPrimeCore_centralizer_graphFixedRootGroup_triD4_two σ ψ y hy3,
      Subgroup.card_bot]
    exact odd_one
  · rw [pPrimeCore_fixSubgroup_graphFixedRootGroup_triD4_two_outer σ hK hσ x hx3 hin,
      Subgroup.card_bot]
    exact odd_one

theorem oddCoreFact_three_of_trialityD4_two
    {q : TauCeti.PrimePower} (hq : q.card = 2)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :
    OddCoreFact 3 S := by
  have h2 : q.p ^ q.exponent = 2 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  obtain ⟨hp2, hexp⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 h2
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨eK⟩⟩ := exists_catEquiv_trialityD4 q hv
  have hK8 : Nat.card K = (2 ^ 1) ^ 3 := by rw [hK, hp2, hexp]
  have hσ2 : ∀ c, σ c = c ^ (2 ^ 1) := fun c => by rw [hσ c, hp2, hexp]
  obtain ⟨φ8, hcard⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityEven.exists_equiv_trialityGroup8 hp2 hexp hv
  obtain ⟨ψ8⟩ := nonempty_mulEquiv_d4P φ8 hcard
  let ψ : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥d4P := eK.symm.trans ψ8
  exact (oddCoreFact_congr (p := 3) (e.trans eK)).mpr
    (oddCoreFact_three_graphFixedRootGroup_two σ hK8 hσ2 ψ)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
