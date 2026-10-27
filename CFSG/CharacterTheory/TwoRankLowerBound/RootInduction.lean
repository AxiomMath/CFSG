module

public import CFSG.CharacterTheory.TwoRankLowerBound.InvolutionRoots

public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def inducedFunction {G : Type*} [Group G] [Fintype G]
    (subgroup : Subgroup G) (function : subgroup → ℂ) (element : G) : ℂ := by
  classical
  exact (Nat.card subgroup : ℂ)⁻¹ * ∑ conjugator : G,
    if hmember : conjugator⁻¹ * element * conjugator ∈ subgroup then
      function ⟨conjugator⁻¹ * element * conjugator, hmember⟩ else 0

theorem induced_involution_root_supported_function_vanishes
    {G : Type*} [Group G] [Fintype G] (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution)
    (subgroup : Subgroup G) (function : subgroup → ℂ)
    (hsupport : ∀ element : subgroup,
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (left right : G) (hleft : orderOf left = 2) (hright : orderOf right = 2) :
    inducedFunction subgroup function (left * right) = 0 := by
  classical
  unfold inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro conjugator _
  split_ifs with hmember
  · exact hsupport ⟨conjugator⁻¹ * (left * right) * conjugator, hmember⟩
      (involution_product_not_mem_conjugate_rootSet_of_unique_centralizer_involution
        involution left right conjugator horder hleft hright hunique)
  · rfl

theorem induced_root_supported_function_vanishes_on_involution_products
    {G : Type*} [Group G] [Fintype G] (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (left right : G) (hleft : orderOf left = 2) (hright : orderOf right = 2) :
    inducedFunction (Subgroup.centralizer ({involution} : Set G)) function (left * right) = 0 := by
  classical
  unfold inducedFunction
  rw [Finset.sum_eq_zero, mul_zero]
  intro conjugator _
  split_ifs with hmember
  · exact hsupport ⟨conjugator⁻¹ * (left * right) * conjugator, hmember⟩
      (involution_product_not_mem_conjugate_rootSet_of_unique_centralizer_involution
        involution left right conjugator horder hleft hright hunique)
  · rfl

theorem root_supported_involution_pair_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (involutions : Finset G) (hall : ∀ element ∈ involutions, orderOf element = 2) :
    ∑ left ∈ involutions, ∑ right ∈ involutions,
      inducedFunction (Subgroup.centralizer ({involution} : Set G)) function (left * right) = 0 := by
  apply Finset.sum_eq_zero
  intro left hleft
  apply Finset.sum_eq_zero
  intro right hright
  exact induced_root_supported_function_vanishes_on_involution_products involution horder
    hunique function hsupport left right (hall left hleft) (hall right hright)

end CFSG.TwoRankLowerBound.Helpers
