module

public import CFSG.LocalAnalysis.ComponentClassification.SwappedQuasisimpleProduct
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionFixedPoints

public section

namespace CFSG.ComponentClassification.CommutingOrbitFixedInvolution

theorem outside_pair {G : Type*} [Group G] [Finite G] {Index : Type*}
    (factors : Index → Subgroup G)
    (heven : ∀ index, Even (Nat.card (factors index)))
    (hcommutes : Pairwise (fun first second => ⁅factors first, factors second⁆ = ⊥))
    (permutation : Index → Index) (hpermutation : Function.Involutive permutation)
    (automorphism : MulAut G) (hinvolutive : Function.Involutive automorphism)
    (himages : ∀ index, (factors index).map automorphism.toMonoidHom = factors (permutation index))
    (first other : Index) (hotherFirst : other ≠ first)
    (hotherSecond : other ≠ permutation first) :
    ∃ member : G, orderOf member = 2 ∧ automorphism member = member ∧
      member ∈ factors other ⊔ factors (permutation other) ∧
      member ∈ Subgroup.centralizer ((factors first ⊔ factors (permutation first) : Subgroup G) : Set G) := by
  let product := factors other ⊔ (factors other).map automorphism.toMonoidHom
  let localAutomorphism := SwappedQuasisimpleProduct.productAutomorphism
    (factors other) automorphism hinvolutive
  have hlocalInvolutive : Function.Involutive localAutomorphism := by
    intro member
    exact Subtype.ext (hinvolutive member.val)
  have hproductEven : Even (Nat.card product) := even_iff_two_dvd.mpr
    ((even_iff_two_dvd.mp (heven other)).trans
      (Subgroup.card_dvd_of_le (le_sup_left : factors other ≤ product)))
  obtain ⟨member, horder, hfixed⟩ := InvolutionFixedPoints.exists_fixed_involution
    (even_iff_two_dvd.mp hproductEven) localAutomorphism hlocalInvolutive
  have hproduct : member.val ∈ factors other ⊔ factors (permutation other) := by
    have hmem := member.property
    change member.val ∈ factors other ⊔ (factors other).map automorphism.toMonoidHom at hmem
    rwa [himages] at hmem
  refine ⟨member.val, (orderOf_injective product.subtype product.subtype_injective member).trans horder,
    congrArg Subtype.val hfixed, hproduct, ?_⟩
  have himageOtherFirst : permutation other ≠ first := by
    intro heq
    exact hotherSecond ((hpermutation other).symm.trans (congrArg permutation heq))
  have himageOtherSecond : permutation other ≠ permutation first :=
    fun heq => hotherFirst (hpermutation.injective heq)
  have hcentralizes : factors other ⊔ factors (permutation other) ≤
      Subgroup.centralizer ((factors first ⊔ factors (permutation first) : Subgroup G) : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    apply sup_le
    · apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hotherFirst)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes himageOtherFirst)
    · apply Subgroup.le_centralizer_iff.mpr
      apply sup_le
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes hotherSecond)
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcommutes himageOtherSecond)
  exact hcentralizes hproduct

end CFSG.ComponentClassification.CommutingOrbitFixedInvolution
