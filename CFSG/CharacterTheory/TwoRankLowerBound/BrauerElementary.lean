module

public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingSubgroupProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def BrauerElementary (G : Type*) [Group G] : Prop :=
  ∃ (prime : ℕ) (cyclic primary : Subgroup G), Nat.Prime prime ∧ IsCyclic cyclic ∧
    ¬prime ∣ Nat.card cyclic ∧ IsPGroup prime primary ∧
    ∃ hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G),
      Function.Surjective (commutingSubgroupProduct cyclic primary hcommute)

theorem brauerElementary_of_product_equiv {G cyclic primary : Type*}
    [Group G] [Group cyclic] [Group primary] [IsCyclic cyclic]
    (prime : ℕ) (hprime : Nat.Prime prime) (hcoprime : ¬prime ∣ Nat.card cyclic)
    (hprimary : IsPGroup prime primary) (isomorphism : cyclic × primary ≃* G) : BrauerElementary G := by
  let cyclicHom := isomorphism.toMonoidHom.comp (MonoidHom.inl cyclic primary)
  let primaryHom := isomorphism.toMonoidHom.comp (MonoidHom.inr cyclic primary)
  have hcyclicInjective : Function.Injective cyclicHom := by
    intro left right hequal
    exact congrArg Prod.fst (isomorphism.injective hequal)
  have hcyclicCard : Nat.card cyclicHom.range = Nat.card cyclic := by
    let equivalence := MulEquiv.ofBijective cyclicHom.rangeRestrict
      ⟨fun _ _ hequal => hcyclicInjective (congrArg Subtype.val hequal), cyclicHom.rangeRestrict_surjective⟩
    exact Nat.card_congr equivalence.symm.toEquiv
  have hcyclic : IsCyclic cyclicHom.range :=
    isCyclic_of_surjective cyclicHom.rangeRestrict cyclicHom.rangeRestrict_surjective
  have hprimaryGroup : IsPGroup prime primaryHom.range :=
    hprimary.of_surjective primaryHom.rangeRestrict primaryHom.rangeRestrict_surjective
  have hcommute : ∀ first : cyclicHom.range, ∀ second : primaryHom.range,
      Commute (first : G) (second : G) := by
    intro first second
    obtain ⟨left, hleft⟩ := first.property
    obtain ⟨right, hright⟩ := second.property
    rw [← hleft, ← hright]
    change isomorphism (left, 1) * isomorphism (1, right) =
      isomorphism (1, right) * isomorphism (left, 1)
    rw [← map_mul, ← map_mul]
    simp only [Prod.mul_def, one_mul, mul_one]
  refine ⟨prime, cyclicHom.range, primaryHom.range, hprime, hcyclic, ?_, hprimaryGroup, hcommute, ?_⟩
  · rw [hcyclicCard]
    exact hcoprime
  · intro element
    let preimage := isomorphism.symm element
    refine ⟨(⟨cyclicHom preimage.1, ⟨preimage.1, rfl⟩⟩,
      ⟨primaryHom preimage.2, ⟨preimage.2, rfl⟩⟩), ?_⟩
    change isomorphism (preimage.1, 1) * isomorphism (1, preimage.2) = element
    rw [← map_mul]
    simp only [Prod.mul_def, one_mul, mul_one]
    exact isomorphism.apply_symm_apply element

theorem prime_regular_centralizer_product_brauerElementary {G : Type*} [Group G] [Finite G]
    (element : G) (prime : ℕ) [Fact (Nat.Prime prime)] (hregular : Nat.Coprime prime (orderOf element))
    (sylow : Sylow prime (Subgroup.centralizer ({element} : Set G))) :
    let cyclic := Subgroup.zpowers element
    let primary := (sylow : Subgroup (Subgroup.centralizer ({element} : Set G))).map
      (Subgroup.centralizer ({element} : Set G)).subtype
    ∃ hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G),
      Disjoint cyclic primary ∧ BrauerElementary (commutingSubgroupProduct cyclic primary hcommute).range := by
  intro cyclic primary
  obtain ⟨hcommute, hdisjoint⟩ := prime_regular_centralizer_commuting_product element prime hregular sylow
  refine ⟨hcommute, hdisjoint, ?_⟩
  apply brauerElementary_of_product_equiv prime Fact.out _ _
    (commutingSubgroupProductEquiv cyclic primary hcommute hdisjoint)
  · rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hregular
  · exact sylow.isPGroup'.map _

end CFSG.TwoRankLowerBound.Helpers
