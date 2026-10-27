module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.OuterArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Linear
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Unitary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.AGLEmbedding.OuterSylow (mem_inner_of_not_dvd_card_outer mem_inner_of_lie_model_cyc)

section Outer


theorem outerHeisInner_of_fixedOrder (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc) : OuterHeisInner := by
  intro K _ _ hs hnab hcat p hp h5 hpK S hS α hαp hαS
  have : IsSimpleGroup K := hs
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [CFSG.Blueprint.classicalTags] at h
      · simp [CFSG.Blueprint.chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine mem_inner_of_not_dvd_card_outer hp (fun hd => ?_) hαp
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    ·
      have hℓ : ℓ.Prime := hadm.1
      have hq2 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by have := hadm.2.1; omega) ℓ)
      have hN : Nat.card K * lieOrderDivisor t n (ℓ ^ f) = lieOrderNumerator t n (ℓ ^ f) :=
        (hLie K t n ℓ f hadm hmodel).2.1
      have hdiv : ¬ p ∣ lieOrderDivisor t n (ℓ ^ f) := by
        intro hd
        rcases dvd_lieOrderDivisor_cases hp h5 hd with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
        · rcases hS with hab | hle
          · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.n1PSL_holds K n ℓ f
              (hmodel.statedClassicalModel (by decide)) p hp hp2 hpn hpq (fun h => by omega) S
              S.isPGroup' S.not_dvd_index hab
          · have := four_le_factorization_of_dvd_lieOrderDivisor hp h5 hq2 hN hd
            omega
        · rcases hS with hab | hle
          · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.n1PSU_holds K n ℓ f
              (hmodel.statedClassicalModel (by decide)) p hp hp2 hpn hpq (fun h => by omega) S
              S.isPGroup' S.not_dvd_index hab
          · have := four_le_factorization_of_dvd_lieOrderDivisor hp h5 hq2 hN hd
            omega
      have hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) := fun h => by omega
      have hT3 : ¬ (t = .trialityD4 ∧ p = 3) := fun h => by omega
      exact mem_inner_of_lie_model_cyc hLie hb hadm hmodel ht hp hp2 hpK hdiv hD4 hT3 S.isPGroup'
        S.not_dvd_index hαp hαS
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem outerHeisInner_holds : OuterHeisInner :=
  outerHeisInner_of_fixedOrder CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds

end Outer

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
