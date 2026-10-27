module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.NoninvertingSection

public section

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators

theorem nonreal_primary_section_block_involution_product_vanishing {G : Type*} [Group G]
    [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (blockLabel : basis.index) {a b u : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hu : ∃ e : ℕ, orderOf u = p ^ e)
    (hreal : ¬ IsConj u u⁻¹) (r : G) (hr : r ∈ Subgroup.centralizer {u})
    (hrp : Nat.Coprime p (orderOf r)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        (basis.representation χ).character a * (basis.representation χ).character b *
          (basis.representation χ).character (u * r) / (basis.representation χ).character 1 =
      0 ∧
    ∀ g : G, ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) blockLabel,
        (basis.representation χ).character a * (basis.representation χ).character b *
          (basis.representation χ).character (g * (u * r) * g⁻¹) /
            (basis.representation χ).character 1 = 0 := by
  obtain ⟨e, he⟩ := hu
  have hsq : ∀ x : G, orderOf x = 2 → x * x = 1 := fun x hx => by
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hnoinv : ∀ t : G, IsConj a t → t * u * t⁻¹ ≠ u⁻¹ := fun t _ htu =>
    hreal (isConj_iff.mpr ⟨t, htu⟩)
  have hzero := (CFSG.LyonsUnitaryFour.brauer_noninverting_block_section_vanishing basis ideal p
    blockLabel a b u (hsq a ha) (hsq b hb) e (by rw [he]) hnoinv).1 r hr hrp
  refine ⟨hzero, fun g => ?_⟩
  rw [← hzero]
  refine Finset.sum_congr rfl fun χ _ => ?_
  simp only [FiniteComplexRepresentation.character, Representation.char_conj]

end CFSG.Semidihedral.Principal
