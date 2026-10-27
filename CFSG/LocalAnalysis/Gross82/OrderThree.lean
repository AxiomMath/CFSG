module

public import CFSG.LocalAnalysis.Gross82.Basic
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundHolds
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowCases
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.Gross82

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer equivalence)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 (R891GrossCore)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf
open CFSG.Blueprint (LieModel classicalTags chevalleyExceptionalTags reeTitsTags)

@[expose] def GrossThreeInnerOrderThree (K : Type*) [Group K] : Prop :=
  ∀ α : MulAut K, α ^ 3 = 1 → ∀ P : Sylow 3 K, (∀ x ∈ (P : Subgroup K), α x = x) → α ∈ inner K

@[expose] def R891GrossCoreOrderThree : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    IsSimpleGroup K → Subgroup.center K = ⊥ → CFSG.Open.IsCatalogGroup K → 3 ∣ Nat.card K →
      ∀ α : MulAut K, α ^ 3 = 1 →
        ∀ P : Subgroup K, IsSylowOf 3 P ⊤ → (∀ x ∈ P, α x = x) →
          ∃ t ∈ P, α = MulAut.conj t

theorem orderOf_eq_three_pow_of_pow_three_eq_one {G : Type*} [Monoid G] {α : G}
    (hα : α ^ 3 = 1) : ∃ k : ℕ, orderOf α = 3 ^ k := by
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hα) with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

theorem exists_mul_ne_mul_of_center_eq_bot {K : Type*} [Group K] [Nontrivial K]
    (hZ : Subgroup.center K = ⊥) : ∃ a b : K, a * b ≠ b * a := by
  by_contra hc'
  have hc : ∀ a b : K, a * b = b * a := fun a b => by_contra fun h => hc' ⟨a, b, h⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne K
  have hone : ∀ z : K, z = 1 := fun z => by
    have hz : z ∈ Subgroup.center K := Subgroup.mem_center_iff.2 fun g => hc g z
    rw [hZ] at hz
    exact Subgroup.mem_bot.1 hz
  exact hxy ((hone x).trans (hone y).symm)

theorem mem_inner_of_pow_three_of_lieModel (hLie : LieOrderFormulasInput)
    (hb : CFSG.AGLEmbedding.OuterSylow.OuterFixedOrderBound)
    {K : Type} [Group K] [Finite K] {t : StatedLieTag} {n ℓ f : ℕ}
    (hadm : StatedLieAdmissible t n ℓ f) (hmodel : LieModel K t n ℓ f) (ht : t ≠ .Tits)
    (hres : (3 ∣ lieOrderDivisor t n (ℓ ^ f) ∨ (t = .POmegaPlus ∧ n = 4)) →
      GrossThreeInnerOrderThree K)
    (h3 : 3 ∣ Nat.card K) {α : MulAut K} (hα : α ^ 3 = 1) {P : Subgroup K}
    (hP : IsSylowOf 3 P ⊤) (hfix : ∀ x ∈ P, α x = x) : α ∈ inner K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_isSylowOf_top hP
  have hfixQ : ∀ x ∈ (Q : Subgroup K), α x = x := fun x hx => hfix x (hQ ▸ hx)
  by_cases hr : 3 ∣ lieOrderDivisor t n (ℓ ^ f) ∨ (t = .POmegaPlus ∧ n = 4)
  · exact hres hr α hα Q hfixQ
  have hdiv : ¬ 3 ∣ lieOrderDivisor t n (ℓ ^ f) := fun h => hr (Or.inl h)
  have hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ 3 = 3) := fun h => hr (Or.inr ⟨h.1, h.2.1⟩)
  exact CFSG.AGLEmbedding.OuterSylow.mem_inner_of_lie_model hLie hb hadm hmodel ht
    Nat.prime_three (by norm_num) h3 hdiv hD4 Q.isPGroup' Q.not_dvd_index hα hfixQ

section TitsOrderThree

theorem mem_inner_of_pow_three_of_tits {K : Type} [Group K] [Finite K] {n ℓ f : ℕ}
    (hmodel : LieModel K .Tits n ℓ f) {α : MulAut K} (hα : α ^ 3 = 1) : α ∈ inner K := by
  rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
  · simp [classicalTags] at h
  · simp [chevalleyExceptionalTags] at h
  · obtain ⟨k, hk⟩ :=
      (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier K ℓ f hree).1.exists_card_eq
    refine CFSG.AGLEmbedding.OuterSylow.mem_inner_of_not_dvd_card_outer Nat.prime_three
      (fun hd => ?_) hα
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  · cases h

end TitsOrderThree

section Residual

theorem r891GrossCoreOrderThree_of_residual
    (hres : ∀ (K : Type) [Group K] [Finite K] (t : StatedLieTag) (n ℓ f : ℕ),
      StatedLieAdmissible t n ℓ f → LieModel K t n ℓ f →
        (3 ∣ lieOrderDivisor t n (ℓ ^ f) ∨ (t = .POmegaPlus ∧ n = 4)) →
          IsSimpleGroup K → Subgroup.center K = ⊥ → 3 ∣ Nat.card K →
            GrossThreeInnerOrderThree K) :
    R891GrossCoreOrderThree := by
  intro K _ _ hs hZ hcat h3 α hα P hP hfix
  have hnab := exists_mul_ne_mul_of_center_eq_bot hZ
  refine exists_eq_conj_of_isSylowOf_top_of_mem_inner hZ α
    (orderOf_eq_three_pow_of_pow_three_eq_one hα) P hP hfix ?_
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge K hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine CFSG.AGLEmbedding.OuterSylow.mem_inner_of_not_dvd_card_outer Nat.prime_three ?_ hα
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 3 Nat.prime_three
      (by norm_num)
  · by_cases ht : t = .Tits
    · subst ht
      exact mem_inner_of_pow_three_of_tits hmodel hα
    · exact mem_inner_of_pow_three_of_lieModel
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
        CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBound_holds hadm hmodel ht
        (fun hr => hres K t n ℓ f hadm hmodel hr hs hZ h3) h3 hα hP hfix
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine CFSG.AGLEmbedding.OuterSylow.mem_inner_of_not_dvd_card_outer Nat.prime_three ?_ hα
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s 3 Nat.prime_three (by norm_num)

end Residual

end CFSG.LocalAnalysis.Gross82
