module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.OuterArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.GlueGroup
public import CFSG.HardMathSupport.Lang.Coordinator.ONanOuterSylowCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.AGLEmbedding.OuterSylow (mem_inner_of_not_dvd_card_outer mem_inner_of_lie_model_cyc)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

section Outer


theorem outerThreeInner_of_fixedOrder (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc) : OuterThreeInner := by
  intro K _ _ hs hnab hcat S hSn hfac α hα3 hαS
  have : IsSimpleGroup K := hs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS3 : (Nat.card K).factorization 3 = 3 := by
    have h1 := pow_three_le_card_of_nonabelian S.isPGroup' hSn
    rw [S.card_eq_multiplicity] at h1
    have : 3 ≤ (Nat.card K).factorization 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega
  have hpK : 3 ∣ Nat.card K :=
    (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').2 (by omega)
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine mem_inner_of_not_dvd_card_outer Nat.prime_three ?_ hα3
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 3 Nat.prime_three
      (by norm_num)
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [CFSG.Blueprint.classicalTags] at h
      · simp [CFSG.Blueprint.chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine mem_inner_of_not_dvd_card_outer Nat.prime_three (fun hd => ?_) hα3
        rw [hk] at hd
        exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
      · cases h
    · have hℓ : ℓ.Prime := hadm.1
      have hq2 : 2 ≤ ℓ ^ f :=
        hℓ.two_le.trans (Nat.le_self_pow (by have := hadm.2.1; omega) ℓ)
      have hN : Nat.card K * lieOrderDivisor t n (ℓ ^ f) = lieOrderNumerator t n (ℓ ^ f) :=
        (hLie K t n ℓ f hadm hmodel).2.1
      obtain ⟨hdiv, hD4, hT3⟩ := three_lie_conditions hq2 hN hS3
      exact mem_inner_of_lie_model_cyc hLie hb hadm hmodel ht Nat.prime_three (by norm_num) hpK
        hdiv (fun h => hD4 ⟨h.1, h.2.1⟩) (fun h => hT3 h.1) S.isPGroup' S.not_dvd_index hα3 hαS
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine mem_inner_of_not_dvd_card_outer Nat.prime_three ?_ hα3
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s 3 Nat.prime_three (by norm_num)

theorem outerThreeInner_holds : OuterThreeInner :=
  outerThreeInner_of_fixedOrder CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds

end Outer

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
