module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingFusion

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

theorem odd_product_involution_conjugates (first second : Involution G)
    (hodd : Odd (orderOf ((first : G) * second))) (hne : first ≠ second) :
    ∃ conjugator : Involution G,
      (conjugator : G) ∈ Subgroup.closure ({(first : G), (second : G)} : Set G) ∧
      conjugateInvolution (conjugator : G) first = second := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨exponent, hconj⟩ := odd_product_conjugates first second hodd
  let rotation : G := ((first : G) * second) ^ exponent
  let reflection : G := rotation * first
  have hreflects : conjugateInvolution reflection first = second := by
    rw [conjugateInvolution_mul, conjugateInvolution_self]
    exact hconj
  have hsquare : reflection ^ 2 = 1 := by
    change (rotation * first) ^ 2 = 1
    rw [pow_two, mul_assoc]
    have hinverts : (first : G) * rotation * first = rotation⁻¹ := by
      simpa only [MulAut.conj_apply, inv_eq_self_of_orderOf_eq_two first.property]
        using conjugate_pow_eq_inv first second exponent
    rw [← mul_assoc (first : G) rotation, hinverts, mul_inv_cancel]
  have hnonidentity : reflection ≠ 1 := by
    intro hone
    rw [hone, conjugateInvolution_one] at hreflects
    exact hne hreflects
  refine ⟨⟨reflection, orderOf_eq_prime hsquare hnonidentity⟩, ?_, hreflects⟩
  have hfirst : (first : G) ∈
      Subgroup.closure ({(first : G), (second : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hsecond : (second : G) ∈
      Subgroup.closure ({(first : G), (second : G)} : Set G) :=
    Subgroup.subset_closure (by simp)
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mul_mem _ hfirst hsecond) exponent)
    hfirst

theorem stronglyEmbedded_crossing_involution_conjugates [Finite G]
    (subgroup : Subgroup G) (hstrong : IsStronglyEmbedded subgroup)
    (inside outside : Involution G) (hinside : (inside : G) ∈ subgroup)
    (houtside : (outside : G) ∉ subgroup) :
    ∃ conjugator : Involution G, (conjugator : G) ∉ subgroup ∧
      (conjugator : G) ∈ Subgroup.closure ({(inside : G), (outside : G)} : Set G) ∧
      conjugateInvolution (conjugator : G) inside = outside := by
  obtain ⟨conjugator, hgenerated, hconj⟩ := odd_product_involution_conjugates inside outside
    (stronglyEmbedded_outside_involution_product_odd subgroup hstrong inside outside
      hinside houtside) (by intro heq; exact houtside (heq ▸ hinside))
  refine ⟨conjugator, ?_, hgenerated, hconj⟩
  intro hmem
  apply houtside
  rw [← hconj]
  exact subgroup.mul_mem (subgroup.mul_mem hmem hinside) (subgroup.inv_mem hmem)

abbrev OutsideInvolution (subgroup : Subgroup G) :=
  {involution : Involution G // (involution : G) ∉ subgroup}

@[expose] def outsideInvolutionConjugation (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (inside : Involution G)
    (hinside : (inside : G) ∈ subgroup) :
    OutsideInvolution subgroup → OutsideInvolution subgroup :=
  fun outside => ⟨conjugateInvolution (outside.val : G) inside,
    fun hmem => outside.property (stronglyEmbedded_involution_conjugator_mem subgroup
      hstrong inside hinside (outside.val : G) hmem)⟩

theorem outsideInvolutionConjugation_bijective [Finite G] (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (inside : Involution G)
    (hinside : (inside : G) ∈ subgroup) :
    Function.Bijective (outsideInvolutionConjugation subgroup hstrong inside hinside) := by
  have hsurjective : Function.Surjective
      (outsideInvolutionConjugation subgroup hstrong inside hinside) := by
    intro outside
    obtain ⟨conjugator, hnotmem, _, hconj⟩ := stronglyEmbedded_crossing_involution_conjugates
      subgroup hstrong inside outside.val hinside outside.property
    exact ⟨⟨conjugator, hnotmem⟩, Subtype.ext hconj⟩
  exact ⟨hsurjective.injective_of_finite (Equiv.refl _), hsurjective⟩

theorem stronglyEmbedded_crossing_unique_involution_conjugator [Finite G]
    (subgroup : Subgroup G) (hstrong : IsStronglyEmbedded subgroup)
    (inside outside : Involution G) (hinside : (inside : G) ∈ subgroup)
    (houtside : (outside : G) ∉ subgroup) :
    ∃! conjugator : Involution G, conjugateInvolution (conjugator : G) inside = outside := by
  obtain ⟨conjugator, hnotmem, _, hconj⟩ := stronglyEmbedded_crossing_involution_conjugates
    subgroup hstrong inside outside hinside houtside
  refine ⟨conjugator, hconj, ?_⟩
  intro other hother
  have hothernotmem : (other : G) ∉ subgroup := by
    intro hmem
    apply houtside
    rw [← hother]
    exact subgroup.mul_mem (subgroup.mul_mem hmem hinside) (subgroup.inv_mem hmem)
  have heq : outsideInvolutionConjugation subgroup hstrong inside hinside
      ⟨other, hothernotmem⟩ = outsideInvolutionConjugation subgroup hstrong inside hinside
      ⟨conjugator, hnotmem⟩ := Subtype.ext (hother.trans hconj.symm)
  exact congrArg Subtype.val
    ((outsideInvolutionConjugation_bijective subgroup hstrong inside hinside).1 heq)

end CFSG.DisconnectedInvolutionGraph.Helpers
