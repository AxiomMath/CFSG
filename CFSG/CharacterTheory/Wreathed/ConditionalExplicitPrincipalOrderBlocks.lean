module

public import CFSG.CharacterTheory.Wreathed.ConditionalLinearAugmentationTwistsBlocks
public import CFSG.CharacterTheory.CentralInvolutionParity

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

variable {E : Type} [Group E] [Fintype E]

omit [Fintype E] in
theorem blocksIsPPart_two_of_orderOf_eq_two {g : E} (hg : orderOf g = 2) : BlocksIsPPart 2 g g :=
  ⟨1, mul_one g, one_mul g, ⟨1, by rw [hg, pow_one]⟩, by rw [orderOf_one]; exact one_pos,
    by rw [orderOf_one]; exact Nat.coprime_one_left 2⟩

theorem blocksIsPPart_two_of_odd {w : E} (hw : Odd (orderOf w)) : BlocksIsPPart 2 w 1 :=
  ⟨w, one_mul w, mul_one w, ⟨0, by rw [orderOf_one, pow_zero]⟩, orderOf_pos w,
    Nat.coprime_two_right.mpr hw⟩

theorem blockOf_eq_image_coefficientBlock (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (principal : basis.index) :
    BlocksBlockOf ideal E (basis.representation principal).character =
      (fun l => (basis.representation l).character) ''
        ↑(coefficientBlock basis (localizedComplexIntegerRing ideal) principal) := by
  ext χ
  constructor
  · intro hχ
    obtain ⟨l, hl⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis hχ.1
    refine ⟨l, ?_, hl⟩
    rw [Finset.mem_coe, mem_coefficientBlock_iff_mem_blockOf, hl]
    exact hχ
  · rintro ⟨l, hl, rfl⟩
    exact (mem_coefficientBlock_iff_mem_blockOf basis ideal principal l).mp hl

theorem sum_coefficientBlock_mul_star_eq_zero (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {g w gp wp : E}
    (hg : BlocksIsPPart 2 g gp) (hw : BlocksIsPPart 2 w wp) (hgw : ¬ IsConj gp wp) :
    ∑ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation l).character g *
        starRingEnd ℂ ((basis.representation l).character w) = 0 := by
  have hB : BlocksIsBlock ideal E
      (BlocksBlockOf ideal E (basis.representation principal).character) :=
    ⟨_, CFSG.BlockBasics.basis_character_mem_irr basis principal, rfl⟩
  have h := CFSG.BlockSectionOrthogonality.block_section_orthogonality 2 Nat.prime_two ideal
    inferInstance (CFSG.BlockBasics.prime_mem_of_charP 2 ideal) E _ hB g w gp wp hg hw hgw
  rw [blockOf_eq_image_coefficientBlock basis ideal principal,
    finsum_mem_image (fun l _ l' _ h => basis.distinct h), finsum_mem_coe_finset] at h
  exact h

theorem involution_moment_term {χ : E → ℂ} (hχ : χ ∈ BlocksIrr E) {x y : E}
    (hx : x ∈ Subgroup.center E) (hx2 : orderOf x = 2) (hy : IsConj y (x * y)) (D : ℂ)
    (z : E) :
    (χ x + D * χ y) ^ 2 * χ (x * z) / χ 1 =
      (χ x + 2 * D * χ y + D ^ 2 * χ y ^ 2 / χ 1) * χ z := by
  obtain ⟨hsign, hmul, -⟩ := (CFSG.CentralInvolution.central_involution_character_parity x hx
    hx2).1 χ hχ
  set s := CFSG.CentralInvolution.centralInvolutionSign x χ with hs
  have h1 : χ 1 ≠ 0 := CFSG.DirectProduct.identity_ne_zero_of_mem hχ
  have hxs : χ x = s * χ 1 := by
    have := hmul 1
    rwa [one_mul] at this
  have hcomm : ∀ h, x * h = h * x := fun h => (Subgroup.mem_center_iff.mp hx h).symm
  have hxz : χ (x * z) = s * χ z := by rw [hcomm, hmul]
  have hclass : ∀ g c : E, χ (c * g * c⁻¹) = χ g := by
    obtain ⟨V, i₁, i₂, i₃, ρ, -, hρ⟩ := hχ
    intro g c
    rw [← hρ]
    exact Representation.char_conj ρ g c
  have hys : χ y = s * χ y := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    have h2 : χ y = χ (x * y) := by rw [← hc, hclass]
    rw [hcomm, hmul] at h2
    exact h2
  have hs2 : s ^ 2 = 1 := by rcases hsign with h | h <;> rw [h] <;> norm_num
  rw [hxz, hxs, div_eq_iff h1]
  field_simp
  linear_combination (χ z * s * χ 1 ^ 2 + 2 * χ z * χ 1 * D * χ y) * hs2 -
    (χ z * D ^ 2 * χ y) * hys

theorem sum_involution_moment_eq (basis : FiniteIrreducibleCharacterBasis E)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {x y : E}
    (hx : x ∈ Subgroup.center E) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2)
    (hy : IsConj y (x * y)) (D : ℂ) {z : E} (hz : Odd (orderOf z)) :
    ∑ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((basis.representation l).character x + D * (basis.representation l).character y) ^ 2 *
        (basis.representation l).character (x * z) / (basis.representation l).character 1 =
      D ^ 2 * ∑ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation l).character y ^ 2 * (basis.representation l).character z /
          (basis.representation l).character 1 := by
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hzinv : Odd (orderOf z⁻¹) := by rwa [orderOf_inv]
  have hne : ∀ {g : E}, orderOf g = 2 → ¬ IsConj g 1 := by
    intro g hg h
    rw [isConj_one_left] at h
    rw [h, orderOf_one] at hg
    norm_num at hg
  have hconj : ∀ l, starRingEnd ℂ ((basis.representation l).character z⁻¹) =
      (basis.representation l).character z := by
    intro l
    rw [CFSG.BlockSectionOrthogonality.Helpers.irreducible_character_inversion
      (CFSG.BlockBasics.basis_character_mem_irr basis l), Complex.conj_conj]
  have hx0 := sum_coefficientBlock_mul_star_eq_zero basis ideal principal
    (blocksIsPPart_two_of_orderOf_eq_two hx2) (blocksIsPPart_two_of_odd hzinv) (hne hx2)
  have hy0 := sum_coefficientBlock_mul_star_eq_zero basis ideal principal
    (blocksIsPPart_two_of_orderOf_eq_two hy2) (blocksIsPPart_two_of_odd hzinv) (hne hy2)
  simp only [hconj] at hx0 hy0
  rw [Finset.sum_congr rfl fun l _ => involution_moment_term
    (CFSG.BlockBasics.basis_character_mem_irr basis l) hx hx2 hy D z]
  have hsplit : ∀ l, ((basis.representation l).character x +
      2 * D * (basis.representation l).character y +
      D ^ 2 * (basis.representation l).character y ^ 2 / (basis.representation l).character 1) *
        (basis.representation l).character z =
      (basis.representation l).character x * (basis.representation l).character z +
        2 * D * ((basis.representation l).character y * (basis.representation l).character z) +
        D ^ 2 * ((basis.representation l).character y ^ 2 *
          (basis.representation l).character z / (basis.representation l).character 1) :=
    fun l => by ring
  rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hx0, hy0, mul_zero, zero_add, zero_add]

end CFSG.Wreathed
