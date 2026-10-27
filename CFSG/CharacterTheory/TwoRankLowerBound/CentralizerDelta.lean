module

public import CFSG.CharacterTheory.TwoRankLowerBound.InductionPairing
public import CFSG.CharacterTheory.TwoRankLowerBound.AbelianCharacterDelta
public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingSubgroupProduct

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem hom_to_prime_group_eq_one_of_coprime_order {source target : Type*}
    [Group source] [Group target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (hprimary : IsPGroup prime target) (homomorphism : source →* target) (element : source)
    (hcoprime : Nat.Coprime prime (orderOf element)) : homomorphism element = 1 := by
  by_contra hne
  have hdiv := (hprimary.dvd_orderOf hne).trans (orderOf_map_dvd homomorphism element)
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcoprime hdiv

@[expose] noncomputable def commutingProductDelta {G : Type*} [Group G]
    (cyclic primary : Subgroup G)
    (hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G))
    (hdisjoint : Disjoint cyclic primary) (selected : cyclic) :
    (commutingSubgroupProduct cyclic primary hcommute).range → ℂ :=
  fun element => if ((commutingSubgroupProductEquiv cyclic primary hcommute hdisjoint).symm element).1 = selected
    then (Nat.card cyclic : ℂ) else 0

theorem commutingProductDelta_in_span {G : Type*} [Group G] [Finite G]
    (cyclic primary : Subgroup G) [IsCyclic cyclic]
    (hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G))
    (hdisjoint : Disjoint cyclic primary) (selected : cyclic) :
    commutingProductDelta cyclic primary hcommute hdisjoint selected ∈
      algebraicCharacterSpan (commutingSubgroupProduct cyclic primary hcommute).range := by
  let projection := (MonoidHom.fst cyclic primary).comp
    (commutingSubgroupProductEquiv cyclic primary hcommute hdisjoint).symm.toMonoidHom
  let : Fintype cyclic := Fintype.ofFinite cyclic
  have hspan := algebraicCharacterSpan_inflation projection _ (abelian_character_delta_in_algebraic_span selected)
  convert hspan using 1
  funext element
  simp only [commutingProductDelta, Function.comp_apply,
    show projection element = ((commutingSubgroupProductEquiv cyclic primary hcommute hdisjoint).symm element).1
      from rfl]

theorem commutingProductDelta_regular_value {G : Type*} [Group G]
    (cyclic primary : Subgroup G)
    (hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G))
    (hdisjoint : Disjoint cyclic primary) (selected : cyclic)
    (prime : ℕ) [Fact (Nat.Prime prime)] (hprimary : IsPGroup prime primary)
    (element : (commutingSubgroupProduct cyclic primary hcommute).range)
    (hregular : Nat.Coprime prime (orderOf (element : G))) :
    commutingProductDelta cyclic primary hcommute hdisjoint selected element =
      if (element : G) = selected then (Nat.card cyclic : ℂ) else 0 := by
  let equivalence := commutingSubgroupProductEquiv cyclic primary hcommute hdisjoint
  let projection := (MonoidHom.snd cyclic primary).comp equivalence.symm.toMonoidHom
  have hregularLocal : Nat.Coprime prime (orderOf element) := by
    rw [← Subgroup.orderOf_coe]
    exact hregular
  have hsecond : (equivalence.symm element).2 = 1 :=
    hom_to_prime_group_eq_one_of_coprime_order prime hprimary projection element hregularLocal
  have helement : (element : G) = ((equivalence.symm element).1 : G) := by
    have hequal := commutingSubgroupProductEquiv_apply cyclic primary hcommute hdisjoint (equivalence.symm element)
    change (equivalence (equivalence.symm element) : G) = _ at hequal
    rw [equivalence.apply_symm_apply, hsecond, Subgroup.coe_one, mul_one] at hequal
    exact hequal
  have heq : (equivalence.symm element).1 = selected ↔ (element : G) = selected := by
    rw [helement]
    exact Subtype.ext_iff
  change (if (equivalence.symm element).1 = selected then (Nat.card cyclic : ℂ) else 0) = _
  simp only [heq]

theorem induced_regular_delta_value {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (selected : G) (hselected : selected ∈ subgroup) (constant : ℂ)
    (function : subgroup → ℂ)
    (hvalues : ∀ conjugator : G,
      ∀ hmember : conjugator⁻¹ * selected * conjugator ∈ subgroup,
      function ⟨conjugator⁻¹ * selected * conjugator, hmember⟩ =
        if conjugator⁻¹ * selected * conjugator = selected then constant else 0) :
    inducedFunction subgroup function selected =
      (Nat.card subgroup : ℂ)⁻¹ * (Nat.card (Subgroup.centralizer ({selected} : Set G)) : ℂ) * constant := by
  have hterm : ∀ conjugator : G,
      (if hmember : conjugator⁻¹ * selected * conjugator ∈ subgroup then
        function ⟨conjugator⁻¹ * selected * conjugator, hmember⟩ else 0) =
      if conjugator ∈ Subgroup.centralizer ({selected} : Set G) then constant else 0 := by
    intro conjugator
    have heq : conjugator⁻¹ * selected * conjugator = selected ↔
        conjugator ∈ Subgroup.centralizer ({selected} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro hequal member hmember
        have hmemberEq : member = selected := Set.mem_singleton_iff.mp hmember
        rw [hmemberEq]
        have hequal' := congrArg (fun value => conjugator * value) hequal
        simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hequal'
      · intro hcommutes
        have hcommute := hcommutes selected (Set.mem_singleton selected)
        calc
          conjugator⁻¹ * selected * conjugator = conjugator⁻¹ * (selected * conjugator) := mul_assoc _ _ _
          _ = conjugator⁻¹ * (conjugator * selected) := by rw [hcommute]
          _ = selected := by group
    by_cases hmember : conjugator⁻¹ * selected * conjugator ∈ subgroup
    · rw [dite_eq_left hmember, hvalues conjugator hmember, heq]
    · have hnot : conjugator ∉ Subgroup.centralizer ({selected} : Set G) := by
        intro hcentral
        apply hmember
        rw [heq.mpr hcentral]
        exact hselected
      rw [dite_eq_right hmember, ite_eq_right hnot]
  unfold inducedFunction
  simp_rw [hterm]
  have hsum := subgroup_conditional_sum (Subgroup.centralizer ({selected} : Set G))
    (fun _member => constant)
  simp only [dite_eq_ite, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hsum
  rw [hsum]
  ring

end CFSG.TwoRankLowerBound.Helpers
