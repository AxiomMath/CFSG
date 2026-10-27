module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingLocal

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem stronglyEmbedded_involution_conjugator_mem (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (involution : Involution G)
    (hmem : (involution : G) ∈ subgroup) (g : G)
    (hconj : (conjugateInvolution g involution : G) ∈ subgroup) : g ∈ subgroup := by
  by_contra houtside
  apply stronglyEmbedded_intersection_no_involution subgroup hstrong g houtside
    (conjugateInvolution g involution) (conjugateInvolution g involution).property
  refine ⟨hconj, ?_⟩
  change (MulAut.conj g⁻¹) ((MulAut.conj g) involution) ∈ subgroup
  simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel,
    mul_one, mul_inv_cancel, one_mul, inv_mul_cancel_left] using hmem

theorem stronglyEmbedded_involution_centralizer_le (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (involution : Involution G)
    (hmem : (involution : G) ∈ subgroup) :
    Subgroup.centralizer ({(involution : G)} : Set G) ≤ subgroup := by
  intro g hcentralizes
  apply stronglyEmbedded_involution_conjugator_mem subgroup hstrong involution hmem g
  change g * (involution : G) * g⁻¹ ∈ subgroup
  rw [Subgroup.mem_centralizer_singleton_iff.mp hcentralizes, mul_assoc, mul_inv_cancel,
    mul_one]
  exact hmem

theorem stronglyEmbedded_outside_involution_product_odd [Finite G]
    (subgroup : Subgroup G) (hstrong : IsStronglyEmbedded subgroup)
    (inside outside : Involution G) (hinside : (inside : G) ∈ subgroup)
    (houtside : (outside : G) ∉ subgroup) :
    Odd (orderOf ((inside : G) * outside)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨common, hinsidecomm, houtsidecomm⟩ :=
    even_product_common_involution inside outside heven
  have hcommon : (common : G) ∈ subgroup :=
    stronglyEmbedded_involution_centralizer_le subgroup hstrong inside hinside
      (Subgroup.mem_centralizer_singleton_iff.mpr hinsidecomm.symm)
  exact houtside (stronglyEmbedded_involution_centralizer_le subgroup hstrong common hcommon
    (Subgroup.mem_centralizer_singleton_iff.mpr houtsidecomm))

theorem stronglyEmbedded_exists_involution [Finite G] (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) :
    ∃ involution : Involution G, (involution : G) ∈ subgroup := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨element, horder⟩ := exists_prime_orderOf_dvd_card' (G := subgroup) 2
    (even_iff_two_dvd.mp hstrong.2.1)
  exact ⟨⟨element, (Subgroup.orderOf_coe element).trans horder⟩, element.property⟩

theorem stronglyEmbedded_exists_outside_involution [Finite G] (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) :
    ∃ involution : Involution G, (involution : G) ∉ subgroup := by
  classical
  have houtside : ∃ g : G, g ∉ subgroup := by
    by_contra hnone
    apply hstrong.1
    apply top_unique
    intro g _
    exact Classical.byContradiction (fun hnot => hnone ⟨g, hnot⟩)
  obtain ⟨g, hg⟩ := houtside
  obtain ⟨involution, hmem⟩ := stronglyEmbedded_exists_involution subgroup hstrong
  refine ⟨conjugateInvolution g involution, ?_⟩
  exact fun hconj => hg
    (stronglyEmbedded_involution_conjugator_mem subgroup hstrong involution hmem g hconj)

theorem stronglyEmbedded_involutions_conjugate_within [Finite G]
    (subgroup : Subgroup G) (hstrong : IsStronglyEmbedded subgroup)
    (first second : Involution G) (hfirst : (first : G) ∈ subgroup)
    (hsecond : (second : G) ∈ subgroup) :
    ∃ g : G, g ∈ subgroup ∧ conjugateInvolution g first = second := by
  obtain ⟨outside, houtside⟩ := stronglyEmbedded_exists_outside_involution subgroup hstrong
  obtain ⟨firstExponent, hfirstConj⟩ := odd_product_conjugates first outside
    (stronglyEmbedded_outside_involution_product_odd subgroup hstrong first outside
      hfirst houtside)
  obtain ⟨secondExponent, hsecondConj⟩ := odd_product_conjugates second outside
    (stronglyEmbedded_outside_involution_product_odd subgroup hstrong second outside
      hsecond houtside)
  let firstConjugator : G := ((first : G) * outside) ^ firstExponent
  let secondConjugator : G := ((second : G) * outside) ^ secondExponent
  have hconj : conjugateInvolution (secondConjugator⁻¹ * firstConjugator) first =
      second := by
    rw [conjugateInvolution_mul, show conjugateInvolution firstConjugator first = outside
      from hfirstConj]
    rw [show outside = conjugateInvolution secondConjugator second from hsecondConj.symm,
      ← conjugateInvolution_mul, inv_mul_cancel, conjugateInvolution_one]
  refine ⟨secondConjugator⁻¹ * firstConjugator, ?_, hconj⟩
  apply stronglyEmbedded_involution_conjugator_mem subgroup hstrong first hfirst
  rw [hconj]
  exact hsecond

theorem stronglyEmbedded_all_involutions_conjugate [Finite G]
    (subgroup : Subgroup G) (hstrong : IsStronglyEmbedded subgroup)
    (first second : Involution G) : ∃ g : G, conjugateInvolution g first = second := by
  classical
  obtain ⟨inside, hinside⟩ := stronglyEmbedded_exists_involution subgroup hstrong
  have hto : ∀ involution : Involution G,
      ∃ g : G, conjugateInvolution g inside = involution := by
    intro involution
    by_cases hmem : (involution : G) ∈ subgroup
    · obtain ⟨g, _, hconj⟩ := stronglyEmbedded_involutions_conjugate_within subgroup hstrong
        inside involution hinside hmem
      exact ⟨g, hconj⟩
    · obtain ⟨exponent, hconj⟩ := odd_product_conjugates inside involution
        (stronglyEmbedded_outside_involution_product_odd subgroup hstrong inside involution
          hinside hmem)
      exact ⟨((inside : G) * involution) ^ exponent, hconj⟩
  obtain ⟨firstConjugator, hfirst⟩ := hto first
  obtain ⟨secondConjugator, hsecond⟩ := hto second
  refine ⟨secondConjugator * firstConjugator⁻¹, ?_⟩
  rw [← hfirst, ← conjugateInvolution_mul]
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hsecond

end CFSG.DisconnectedInvolutionGraph.Helpers
