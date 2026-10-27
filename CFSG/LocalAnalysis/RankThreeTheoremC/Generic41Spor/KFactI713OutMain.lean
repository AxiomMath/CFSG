module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutPComp
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.KFactI713OutThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerD4
public import CFSG.HardMathSupport.Lang.Coordinator.ONanOuterSylowCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.OutStructure
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.AGLEmbedding.TwoGenInner (PGoodOut pGoodOut_of_not_dvd_outer pGoodOut_of_catalogGroup d4PGood)

section Heavy


theorem pGoodOut_three_of_cyclic {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K) (T : Sylow 3 K)
    (hT : IsCyclic (T : Subgroup K)) : PGoodOut 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian 3 A → Nat.card A ≤ 3 := fun A hA =>
    CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA
  rcases PlaneCases.catalog_cases (TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine pGoodOut_of_not_dvd_outer Nat.prime_three ?_
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 3 Nat.prime_three
      (by norm_num)
  · exact pGoodOut_three_of_lieModel hA hadm hmodel
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    have hnd := CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s 3 Nat.prime_three
      (by norm_num)
    refine pGoodOut_of_not_dvd_outer Nat.prime_three ?_
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact hnd

theorem pGoodOut_ge_five_of_cyclic {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) : PGoodOut p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := center_eq_bot_of_simple hnab
  have hA : ∀ A : Subgroup K, CFSG.Open.IsElemAbelian p A → Nat.card A ≤ p := fun A hA =>
    CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow T hT hA
  have hrk : CFSG.pRank p K ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_le hp.one_lt fun A _ hA' => by
      rw [pow_one]
      exact hA A hA'
  have hLR : LocalRankLeTwo p K := localRankLeTwo_of_card_le hp hA
  have hp3 : 3 < p := by omega
  refine pGoodOut_of_catalogGroup hnab hcat hp hp5 ?_ ?_ d4PGood
  · intro n ℓ f hcl hdvd
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact not_dvd_gcd_psl_of_pRank hp hp5 hrk (statedClassicalModel_psl_quot hZ hcl) hdvd
    · exact (OddRank.not_localRankLeTwo_psl_odd hp hp3 hℓ2 hcl
        (hdvd.trans (Nat.gcd_dvd_left _ _)) (hdvd.trans (Nat.gcd_dvd_right _ _)) hLR).elim
  · intro n ℓ f hcl hdvd
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact not_dvd_gcd_psu_of_pRank hp hp5 hrk (statedClassicalModel_psu_quot hZ hcl) hdvd
    · exact (OddRank.not_localRankLeTwo_psu_odd hp hp3 hℓ2 hcl
        (hdvd.trans (Nat.gcd_dvd_left _ _)) (hdvd.trans (Nat.gcd_dvd_right _ _)) hLR).elim

theorem pGoodOut_of_cyclic_odd {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) : PGoodOut p K := by
  by_cases hp3 : p = 3
  · subst hp3
    exact pGoodOut_three_of_cyclic hnab hcat T hT
  · exact pGoodOut_ge_five_of_cyclic hnab hcat hp (hp.five_le_of_ne_two_of_ne_three hp2 hp3) T hT

theorem reducedOuterSylow_holds : CFSG.AGLEmbedding.OuterSylow.ReducedOuterSylow :=
  CFSG.AGLEmbedding.OuterSylow.reducedOuterSylow_of_fixedOrderCyc
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds

theorem kFactI713Out_holds : KFactI713Out := by
  intro p hp hp2 K _ _ hs hnab hcat hrk
  haveI : IsSimpleGroup K := hs
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  have hT : IsCyclic (T : Subgroup K) := by
    refine isCyclic_of_pRank_le_one hp hp2 (le_top : (T : Subgroup K) ≤ ⊤) T.isPGroup' ?_
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrk
  refine ⟨fun hS => ?_, ?_⟩
  · exact not_dvd_card_outer_of_sylow_card_eq_prime reducedOuterSylow_holds hp hp2 hnab hcat hS
  · exact exists_normal_pComplement_of_pGoodOut hp (pGoodOut_of_cyclic_odd hnab hcat hp hp2 T hT)

end Heavy

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
