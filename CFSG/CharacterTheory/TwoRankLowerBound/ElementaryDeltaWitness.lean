module

public import CFSG.CharacterTheory.TwoRankLowerBound.ElementaryInductionLattice
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralizerDelta

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem elementary_delta_witness {G : Type*} [Group G] [Fintype G]
    (selected : G) (prime : ℕ) [Fact (Nat.Prime prime)]
    (hregular : Nat.Coprime prime (orderOf selected)) :
    ∃ (function : G → ℂ) (index : ℕ), function ∈ extendedElementaryInductionSpan G ∧
      function selected = index ∧ ¬prime ∣ index := by
  let centralizer := Subgroup.centralizer ({selected} : Set G)
  let sylow : Sylow prime centralizer := Classical.arbitrary (Sylow prime centralizer)
  let cyclic := Subgroup.zpowers selected
  let primary := (sylow : Subgroup centralizer).map centralizer.subtype
  obtain ⟨hcommute, hdisjoint, helementary⟩ :=
    prime_regular_centralizer_product_brauerElementary selected prime hregular sylow
  let elementary := (commutingSubgroupProduct cyclic primary hcommute).range
  let cyclicSelected : cyclic := ⟨selected, Subgroup.mem_zpowers selected⟩
  let localFunction := commutingProductDelta cyclic primary hcommute hdisjoint cyclicSelected
  let function := inducedFunction elementary localFunction
  let index := (sylow : Subgroup centralizer).index
  have hvirtual : function ∈ extendedElementaryInductionSpan G :=
    extended_elementary_induction_mem elementary helementary localFunction
      (commutingProductDelta_in_span cyclic primary hcommute hdisjoint cyclicSelected)
  have hselected : selected ∈ elementary := by
    refine ⟨(cyclicSelected, 1), ?_⟩
    change selected * 1 = selected
    exact mul_one _
  have hvalues : ∀ conjugator : G,
      ∀ hmember : conjugator⁻¹ * selected * conjugator ∈ elementary,
      localFunction ⟨conjugator⁻¹ * selected * conjugator, hmember⟩ =
        if conjugator⁻¹ * selected * conjugator = selected then (Nat.card cyclic : ℂ) else 0 := by
    intro conjugator hmember
    apply commutingProductDelta_regular_value cyclic primary hcommute hdisjoint cyclicSelected prime
      (sylow.isPGroup'.map centralizer.subtype) ⟨_, hmember⟩
    have horder : orderOf (conjugator⁻¹ * selected * conjugator) = orderOf selected := by
      simpa only [MulAut.conj_apply, inv_inv] using (MulAut.conj conjugator⁻¹).orderOf_eq selected
    rw [horder]
    exact hregular
  have hevaluation := induced_regular_delta_value elementary selected hselected (Nat.card cyclic)
    localFunction hvalues
  have helementaryCard : Nat.card elementary = Nat.card cyclic * Nat.card primary :=
    commutingSubgroupProduct_card cyclic primary hcommute hdisjoint
  have hprimaryCard : Nat.card primary = Nat.card (sylow : Subgroup centralizer) :=
    Subgroup.card_map_of_injective centralizer.subtype_injective
  have hcentralizerCard : Nat.card centralizer = Nat.card (sylow : Subgroup centralizer) * index :=
    (sylow : Subgroup centralizer).card_mul_index.symm
  have hcyclicNonzero : (Nat.card cyclic : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hprimaryNonzero : (Nat.card (sylow : Subgroup centralizer) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hvalue : function selected = (index : ℂ) := by
    change inducedFunction elementary localFunction selected = _
    rw [hevaluation, helementaryCard, hprimaryCard, hcentralizerCard, Nat.cast_mul, Nat.cast_mul]
    field_simp
  exact ⟨function, index, hvirtual, hvalue, sylow.not_dvd_index⟩

end CFSG.TwoRankLowerBound.Helpers
