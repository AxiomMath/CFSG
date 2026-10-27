module

public import CFSG.Assembly.Defs

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ElementaryAbelianFour

theorem exists_distinct_involutions {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (helementary : IsElemAbelian 2 subgroup)
    (hcard : Nat.card subgroup = 4) :
    ∃ first second : subgroup, first ≠ 1 ∧ second ≠ 1 ∧ first ≠ second ∧
      first * first = 1 ∧ second * second = 1 ∧ Commute first second ∧ first * second ≠ 1 := by
  classical
  have hnontrivial : Nontrivial subgroup := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsubsingleton
    let : Subsingleton subgroup := hsubsingleton
    have hone : Nat.card subgroup = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    omega
  let : Nontrivial subgroup := hnontrivial
  obtain ⟨first, hfirst⟩ := exists_ne (1 : subgroup)
  have hsecond : ∃ second : subgroup, second ≠ 1 ∧ second ≠ first := by
    by_contra hnone
    have hcases : ∀ member : subgroup, member = 1 ∨ member = first := by
      intro member
      by_cases hone : member = 1
      · exact Or.inl hone
      · exact Or.inr (by by_contra hne; exact hnone ⟨member, hone, hne⟩)
    let encode : subgroup → Bool := fun member => decide (member = 1)
    have hinjective : Function.Injective encode := by
      intro left right heq
      rcases hcases left with hleft | hleft <;> rcases hcases right with hright | hright
      · exact hleft.trans hright.symm
      · subst left
        subst right
        simp [encode, hfirst] at heq
      · subst left
        subst right
        simp [encode, hfirst] at heq
      · exact hleft.trans hright.symm
    have hbound := Nat.card_le_card_of_injective encode hinjective
    have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    omega
  obtain ⟨second, hsecondOne, hsecondFirst⟩ := hsecond
  have hfirstSquare : first * first = 1 := by
    apply Subtype.ext
    change first.val * first.val = 1
    simpa only [pow_two] using helementary.2 first.val first.property
  have hsecondSquare : second * second = 1 := by
    apply Subtype.ext
    change second.val * second.val = 1
    simpa only [pow_two] using helementary.2 second.val second.property
  have hcommutes : Commute first second := by
    exact isMulCommutative_iff.mp helementary.1 first second
  refine ⟨first, second, hfirst, hsecondOne, hsecondFirst.symm, hfirstSquare, hsecondSquare, hcommutes, ?_⟩
  intro hproduct
  have heq : second = first := by
    calc
      second = 1 * second := (one_mul second).symm
      _ = (first * first) * second := by rw [hfirstSquare]
      _ = first * (first * second) := mul_assoc _ _ _
      _ = first := by rw [hproduct, mul_one]
  exact hsecondFirst heq

end CFSG.ComponentClassification.ElementaryAbelianFour
