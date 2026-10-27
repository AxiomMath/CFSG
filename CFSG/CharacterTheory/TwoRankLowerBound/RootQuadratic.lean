module

public import CFSG.CharacterTheory.TwoRankLowerBound.RootInduction
public import CFSG.CharacterTheory.TwoRankLowerBound.ClassSum

public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

theorem character_expansion_quadratic_zero_of_involution_product_vanishing
    {G index : Type*} [Group G] [Fintype G] [Fintype index]
    (involution : G) (horder : orderOf involution = 2)
    (function : G → ℂ)
    (hvanishing : ∀ left right : G, orderOf left = 2 → orderOf right = 2 →
      function (left * right) = 0)
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ℂ (vector label)] [∀ label, FiniteDimensional ℂ (vector label)]
    (representation : ∀ label, Representation ℂ G (vector label))
    [∀ label, (representation label).IsIrreducible]
    (coefficient : index → ℂ)
    (hdegrees : ∀ label, (representation label).character 1 ≠ 0)
    (hexpansion : ∀ element : G,
      function element =
        ∑ label, coefficient label * (representation label).character element) :
    ∑ label, coefficient label * (representation label).character involution ^ 2 /
      (representation label).character 1 = 0 := by
  classical
  let conjugacyClass := Finset.univ.filter (fun element : G => IsConj involution element)
  have hclassinvariant : ∀ conjugator element : G,
      element ∈ conjugacyClass ↔ conjugator * element * conjugator⁻¹ ∈ conjugacyClass := by
    intro conjugator element
    simp only [conjugacyClass, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hconjugate
      exact hconjugate.trans (isConj_iff.mpr ⟨conjugator, rfl⟩)
    · intro hconjugate
      apply hconjugate.trans
      apply isConj_iff.mpr
      refine ⟨conjugator⁻¹, ?_⟩
      group
  have hclassconjugate : ∀ element ∈ conjugacyClass, IsConj involution element := by
    intro element hmember
    exact (Finset.mem_filter.mp hmember).2
  have hclassorders : ∀ element ∈ conjugacyClass, orderOf element = 2 := by
    intro element hmember
    obtain ⟨conjugator, rfl⟩ := isConj_iff.mp (hclassconjugate element hmember)
    rw [← MulAut.conj_apply, (MulAut.conj conjugator).orderOf_eq, horder]
  have hsumzero : ∑ left ∈ conjugacyClass, ∑ right ∈ conjugacyClass,
      function (left * right) = 0 := by
    apply Finset.sum_eq_zero
    intro left hleft
    apply Finset.sum_eq_zero
    intro right hright
    exact hvanishing left right (hclassorders left hleft) (hclassorders right hright)
  have hclassquadratic : ∀ label,
      ∑ left ∈ conjugacyClass, ∑ right ∈ conjugacyClass,
        (representation label).character (left * right) =
        (conjugacyClass.card : ℂ) ^ 2 * (representation label).character involution ^ 2 /
          (representation label).character 1 := by
    intro label
    exact irreducible_conjugacy_class_quadratic_evaluation (representation label) involution
      conjugacyClass hclassinvariant hclassconjugate (hdegrees label)
  have htotalsum : ∑ left ∈ conjugacyClass, ∑ right ∈ conjugacyClass,
      function (left * right) =
      (conjugacyClass.card : ℂ) ^ 2 *
        ∑ label, coefficient label * (representation label).character involution ^ 2 /
          (representation label).character 1 := by
    simp_rw [hexpansion]
    rw [Finset.sum_comm_cycle]
    simp_rw [← Finset.mul_sum, hclassquadratic]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro label _
    ring
  have hclassnonempty : conjugacyClass.Nonempty := by
    refine ⟨involution, ?_⟩
    simp only [conjugacyClass, Finset.mem_filter, Finset.mem_univ, true_and]
    exact IsConj.refl involution
  have hclassne : (conjugacyClass.card : ℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr hclassnonempty))
  rw [htotalsum] at hsumzero
  exact (mul_eq_zero.mp hsumzero).resolve_left hclassne

theorem root_supported_character_expansion_quadratic_zero
    {G index : Type*} [Group G] [Fintype G] [Fintype index]
    (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ℂ (vector label)] [∀ label, FiniteDimensional ℂ (vector label)]
    (representation : ∀ label, Representation ℂ G (vector label))
    [∀ label, (representation label).IsIrreducible]
    (coefficient : index → ℂ)
    (hdegrees : ∀ label, (representation label).character 1 ≠ 0)
    (hexpansion : ∀ element : G,
      inducedFunction (Subgroup.centralizer ({involution} : Set G)) function element =
        ∑ label, coefficient label * (representation label).character element) :
    ∑ label, coefficient label * (representation label).character involution ^ 2 /
      (representation label).character 1 = 0 := by
  exact character_expansion_quadratic_zero_of_involution_product_vanishing involution horder
    (inducedFunction (Subgroup.centralizer ({involution} : Set G)) function)
    (induced_root_supported_function_vanishes_on_involution_products involution horder hunique
      function hsupport) vector representation coefficient hdegrees hexpansion

end CFSG.TwoRankLowerBound.Helpers
