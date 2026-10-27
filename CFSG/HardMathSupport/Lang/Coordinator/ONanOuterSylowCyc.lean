module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowCases
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
public import CFSG.HardMathSupport.Lang.Coordinator.TrialityNine
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowGlue
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.TCB.Final
public import CFSG.Sporadic.Bridge.Catalogue

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.Open (IsElemAbelian IsCatalogGroup)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf
  (lieOrderNumerator lieOrderDivisor lieSylowExponent LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo)
open CFSG.Blueprint (LieModel classicalTags chevalleyExceptionalTags reeTitsTags)

theorem mem_inner_of_lie_model_cyc (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc)
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) (hmodel : CFSG.Blueprint.LieModel K t n ℓ f)
    (ht : t ≠ .Tits) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K)
    (hdiv : ¬ p ∣ lieOrderDivisor t n (ℓ ^ f)) (hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3))
    (hT3 : ¬ (t = .trialityD4 ∧ p = 3))
    {S : Subgroup K} (hS : IsPGroup p S) (hSidx : ¬ p ∣ S.index) {α : MulAut K}
    (hαp : α ^ p = 1) (hαS : ∀ s ∈ S, α s = s) : α ∈ inner K := by
  by_contra hα
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hcard, -⟩ := hLie K t n ℓ f hadm hmodel
  have hN := one_le_lieSylowExponent hadm
  have hℓ : ℓ.Prime := hadm.1
  have hf1 : 1 ≤ f := hadm.2.1
  have hq' : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hnum0 : lieOrderNumerator t n (ℓ ^ f) ≠ 0 := lieOrderNumerator_ne_zero ht hN hq'
  have hdiv0 : lieOrderDivisor t n (ℓ ^ f) ≠ 0 := fun h0 => hnum0 (by rw [← hcard, h0, mul_zero])
  have hSle : S ≤ fixedSubgroup α := fun s hs => hαS s hs
  have hSsyl : Nat.card S = p ^ (Nat.card K).factorization p :=
    (hS.toSylow hSidx).card_eq_multiplicity
  have hdvdC : p ^ (Nat.card K).factorization p ∣ Nat.card (fixedSubgroup α) := by
    rw [← hSsyl]
    exact Subgroup.card_dvd_of_le hSle
  have hnumK : (lieOrderNumerator t n (ℓ ^ f)).factorization p = (Nat.card K).factorization p := by
    rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' hdiv0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hdiv, add_zero]
  obtain ⟨f₀, hf, hfix⟩ := hb K t n ℓ f hadm hmodel ht p hp hp2 hdiv hD4 hT3 α hαp hα
  have hf₀ : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  have hq : 2 ≤ ℓ ^ f₀ := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have hqp : (ℓ ^ f₀) ^ p = ℓ ^ f := by rw [← pow_mul, mul_comm, ← hf]
  have hne : lieOrderNumerator t n (ℓ ^ f₀) ≠ 0 := lieOrderNumerator_ne_zero ht hN hq
  have h1 : (Nat.card K).factorization p ≤ (lieOrderNumerator t n (ℓ ^ f₀)).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).1 (hdvdC.trans hfix)
  have hpnum : p ∣ lieOrderNumerator t n ((ℓ ^ f₀) ^ p) := by
    rw [hqp, ← hcard]
    exact hpK.trans (dvd_mul_right _ _)
  have h2 : (lieOrderNumerator t n (ℓ ^ f₀)).factorization p <
      (lieOrderNumerator t n ((ℓ ^ f₀) ^ p)).factorization p := by
    by_cases ht3 : t = .trialityD4
    · subst ht3
      exact numerator_trialityD4_factorization_lt hp2 hq hpnum
    · exact numerator_factorization_lt hp hp2 ht ht3 hN hq hpnum
  rw [hqp, hnumK] at h2
  omega


section CertB


theorem reducedOuterSylow_of_fixedOrderCyc (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc) : ReducedOuterSylow := by
  intro K _ _ hs hnab hcat p hp hp2 hpK S hSp hSidx hScyc α hαp hαS
  have : IsSimpleGroup K := hs
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center K = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot K hnab
  have hA : ∀ A : Subgroup K, IsElemAbelian p A → Nat.card A ≤ p := fun A hA' =>
    CFSG.AGLEmbedding.card_le_of_isElemAbelian_of_isCyclic_sylow (hSp.toSylow hSidx) hScyc hA'
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
      · simp [classicalTags] at h
      · simp [chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine mem_inner_of_not_dvd_card_outer hp (fun hd => ?_) hαp
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · obtain ⟨hdiv, hD4⟩ := not_dvd_divisor_of_cyclic hadm hmodel hp hp2 hZ hA
      have hT3 : ¬ (t = .trialityD4 ∧ p = 3) := by
        rintro ⟨rfl, rfl⟩
        rcases hmodel with ⟨h, -⟩ | ⟨-, -, hch⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
        · simp [classicalTags] at h
        · obtain ⟨A, hAel, hAc⟩ := CFSG.HardMathSupport.Lang.Coordinator.exists_nine_of_trialityD4 hch
          have h9 := hA A hAel
          rw [hAc] at h9
          norm_num at h9
        · simp [reeTitsTags] at h
        · cases h
      exact mem_inner_of_lie_model_cyc hLie hb hadm hmodel ht hp hp2 hpK hdiv hD4 hT3 hSp hSidx
        hαp hαS
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem kFactOuterSylowInner_of_fixedOrderCyc (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc) :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner :=
  kFactOuterSylowInner_of_reduced (reducedOuterSylow_of_fixedOrderCyc hLie hb)

theorem kFactOuterSylowInner_holds_cyc :
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactOuterSylowInner :=
  kFactOuterSylowInner_of_fixedOrderCyc CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds

end CertB

end CFSG.AGLEmbedding.OuterSylow
