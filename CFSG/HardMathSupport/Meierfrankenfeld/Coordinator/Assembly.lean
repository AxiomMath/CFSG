module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.FStar
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Interfaces
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.LinThreeFour
public import CFSG.RankThree.PartTwo.KFacts.KS14Sz
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiComponent
public import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open Subgroup CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.RankThreeCoreUniqueness.Helpers

theorem citedFFL34BestOffender_of
    (hT1 : OddPrimeCoreExclusion) (hSec : ComponentSectionProp) (hL34 : L34ExclusionProp) :
    AGLEmbedding.CitedFFL34BestOffender := by
  intro X _ _ W _ _ _ ρ hρ hKX hO2 L hLn hLperf hLY A hAel hAbest
  classical
  have : L.Normal := hLn
  have := hAel
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  have hO2L : CFSG.pCore 2 ↥L = ⊥ := by
    have hle := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2)
      (Subgroup.Normal.isSubnormal hLn)
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hle
    exact hle
  refine le_centralizer_of_le_centralizer_genFitting hO2 hA2 ?_
  by_contra hF
  rcases exists_pCore_or_component_of_not_le_centralizer hF with ⟨p, hp, hpA⟩ | ⟨K, hK, hKA⟩
  ·
    have hp2 : p ≠ 2 := by
      rintro rfl
      apply hpA
      rw [hO2L, Subgroup.map_bot]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
    have hp3 : p ≠ 3 := by
      rintro rfl
      apply hpA
      rw [pCore_three_eq_bot hLY, Subgroup.map_bot]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
    have hp5 : 5 ≤ p := by
      have h2 := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hp2
        · exact absurd rfl hp3
        · exact absurd hp (by norm_num)
      · exact h
    set R : Subgroup X := (CFSG.pCore p ↥L).map L.subtype with hR
    have hRp : IsPGroup p R :=
      (show IsPGroup p (CFSG.pCore p ↥L) from CFSG.pCore_isPGroup).map _
    have hRn : R.Normal := by rw [hR]; infer_instance
    have hcomm := hT1 X W ρ hρ hO2 p hp hp5 R A hRp hRn hAel hAbest
    apply hpA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact Subgroup.le_centralizer_iff.mp hcomm
  ·
    set K' : Subgroup X := K.map L.subtype with hK'
    have eK' : ↥K ≃* ↥K' := Subgroup.equivMapOfInjective K L.subtype L.subtype_injective
    have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eK' hK.1
    have hK'c : CFSG.IsComponent K' :=
      ⟨hK'q, Subgroup.IsSubnormal.trans' hK.2 (Subgroup.Normal.isSubnormal hLn)⟩
    have hK'X : CFSG.Open.IsComponentOf K' ⊤ := (CFSG.isComponent_iff_open K').mp hK'c
    have hK'A : ⁅K', A⁆ ≠ ⊥ := by
      intro h
      apply hKA
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      exact Subgroup.le_centralizer_iff.mp h
    obtain ⟨V, _, _, f, E, hV, hf0, hirr, hEN, hE0, hEel, hEq, hoff⟩ :=
      hSec X W ρ hρ hO2 A hAel hAbest K' hK'X hK'A
    rcases component_le_or_sup_eq_top hLY hK with hKY | hKY
    ·
      obtain ⟨hLq, ⟨e⟩⟩ := Family.quasisimple_range_centerQuotientEquiv hK'q f hf0
      have : IsSimpleGroup (↥K' ⧸ Subgroup.center ↥K') := hK'q.2.1
      have hnab : ∃ a b : ↥K' ⧸ Subgroup.center ↥K', a * b ≠ b * a := hK'q.2.2
      have hcat : Assembly.InCatalog (↥K' ⧸ Subgroup.center ↥K') :=
        hKX K' (Subgroup.center ↥K') inferInstance
      have h3 : ¬ 3 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
        intro h3
        have hK3 : Nat.Coprime 3 (Nat.card ↥K) :=
          Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKY)
            (primeComplementCore_coprime 3)
        have hdvd : Nat.card (↥K' ⧸ Subgroup.center ↥K') ∣ Nat.card ↥K := by
          rw [Nat.card_congr eK'.toEquiv]
          exact Subgroup.card_quotient_dvd_card _
        have := Nat.Coprime.coprime_dvd_right hdvd hK3
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at this
        exact this h3
      obtain ⟨f', -, a, ha, K₀, _, _, hf', hK₀, ⟨β⟩⟩ :=
        CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
          (↥K' ⧸ Subgroup.center ↥K') hnab hcat h3
      have : Nontrivial V := hirr.1
      have hK₀' : Nat.card K₀ = 2 ^ (2 * a + 1) := by rw [hK₀, hf']
      have hlt := (Family.suzuki_irreducible_normalizer_excludes a ha hK₀' V hV f.range hLq.1
        hirr.2 (e.trans β)).2.2.2.2 E hE0 hEel hEN
      omega
    ·
      obtain ⟨eK⟩ := nonempty_mulEquiv_quotient_of_sup_eq_top hLY hO2L hK hKY
      have hLinK' : AGLEmbedding.IsLinThreeFour ↥K' :=
        AGLEmbedding.L34FF.isLinThreeFour_of_equiv (eK'.symm.trans eK) hLY
      have hsK' : IsSimpleGroup ↥K' := by
        have := isSimpleGroup_quotient hLY
        exact (eK'.symm.trans eK).isSimpleGroup
      have hfinj : Function.Injective f := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
        · exact (MonoidHom.ker_eq_bot_iff f).mp h
        · exfalso
          apply hf0
          rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]
          exact h
      have hLin : AGLEmbedding.IsLinThreeFour ↥f.range :=
        AGLEmbedding.L34FF.isLinThreeFour_of_equiv (MonoidHom.ofInjective hfinj).symm hLinK'
      have hlt := hL34 V hV f.range E hirr hLin hEN hE0 hEel hEq
      omega

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
