module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalGroupAlgebra
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ModularRadical
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.OrbitCongruence

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem normalPSubgroup_centralChar_vanishes (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (subgroup : Subgroup G) [subgroup.Normal]
    (hpGroup : IsPGroup prime subgroup) {character coefficients : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) (hcoefficients : BlocksIsCentralR m coefficients)
    (hvanishes : ∀ element ∈ Subgroup.centralizer (subgroup : Set G), coefficients element = 0) :
    BlocksCentralChar character coefficients ∈ BlocksLocalMaxIdeal m := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : CharP (localResidueField m hm) prime := localResidueField_charP m hm prime hprime hprimeMem
  let : MulAction subgroup G := {
    smul member element := member.val * element * member.val⁻¹
    one_smul element := by
      change (1 : G) * element * (1 : G)⁻¹ = element
      group
    mul_smul left right element := by
      change (left.val * right.val) * element * (left.val * right.val)⁻¹ =
        left.val * (right.val * element * right.val⁻¹) * left.val⁻¹
      group
  }
  have hfixed : MulAction.fixedPoints subgroup G =
      (Subgroup.centralizer (subgroup : Set G) : Set G) := by
    ext element
    rw [MulAction.mem_fixedPoints]
    change (∀ factor : subgroup, factor • element = element) ↔
      element ∈ Subgroup.centralizer (subgroup : Set G)
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hmember factor hfactor
      have hequal := hmember ⟨factor, hfactor⟩
      change factor * element * factor⁻¹ = element at hequal
      exact (mul_inv_eq_iff_eq_mul).mp hequal
    · intro hmember factor
      change factor.val * element * factor.val⁻¹ = element
      rw [hmember factor.val factor.property, mul_inv_cancel_right]
  have hquotient (factor : subgroup) (element : G) :
      (QuotientGroup.mk' subgroup) (factor • element) = (QuotientGroup.mk' subgroup) element := by
    change (QuotientGroup.mk' subgroup) (factor.val * element * factor.val⁻¹) = _
    rw [map_mul, map_mul, map_inv,
      show (QuotientGroup.mk' subgroup) factor.val = 1 from
        (QuotientGroup.eq_one_iff factor.val).mpr factor.property]
    simp only [one_mul, inv_one, mul_one]
  have hsum (quotient : G ⧸ subgroup) :
      (∑ element : G, if (QuotientGroup.mk' subgroup) element = quotient then coefficients element else 0) ∈
        BlocksLocalMaxIdeal m := by
    let weights : G → ℂ := fun element =>
      if (QuotientGroup.mk' subgroup) element = quotient then coefficients element else 0
    have hlocal : ∀ element, weights element ∈ BlocksLocalRing m := by
      intro element
      unfold weights
      split_ifs
      · exact hcoefficients.1 element
      · exact localRing_zero m hm
    have hinvariant : ∀ factor : subgroup, ∀ element : G, weights (factor • element) = weights element := by
      intro factor element
      change (if (QuotientGroup.mk' subgroup) (factor • element) = quotient then
        coefficients (factor.val * element * factor.val⁻¹) else 0) = _
      rw [hquotient, hcoefficients.2]
    have hcongr := invariant_sum_congr_fixed m hm prime hprime hprimeMem hpGroup weights hlocal hinvariant
    have hzero : (MulAction.fixedPoints subgroup G).indicator weights = 0 := by
      ext element
      rw [hfixed, Set.indicator_apply]
      change (if element ∈ Subgroup.centralizer (subgroup : Set G) then weights element else 0) = 0
      by_cases hmember : element ∈ Subgroup.centralizer (subgroup : Set G)
      · rw [ite_eq_left hmember]
        simp only [weights, hvanishes element hmember, ite_self]
      · rw [ite_eq_right hmember]
    simp only [hzero, Pi.zero_apply, finsum_eq_sum_of_fintype, Finset.sum_const_zero, sub_zero] at hcongr
    exact hcongr
  let reduced := MonoidAlgebra.mapRingHom G (localResidue m hm)
    (localCoefficientAlgebra m hm coefficients hcoefficients.1)
  have hkernel : (MonoidAlgebra.mapDomainAlgHom (localResidueField m hm) (localResidueField m hm)
      (QuotientGroup.mk' subgroup)) reduced = 0 := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro quotient
    simp only [reduced, localCoefficientAlgebra, map_sum, MonoidAlgebra.mapRingHom_single,
      MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, MonoidAlgebra.coeff_sum,
      Finset.sum_apply', MonoidAlgebra.coeff_single, Finsupp.single_apply, MonoidAlgebra.coeff_zero,
      Finsupp.zero_apply]
    let localWeights : G → localCoefficientSubring m hm := fun element =>
      if (QuotientGroup.mk' subgroup) element = quotient then
        ⟨coefficients element, hcoefficients.1 element⟩ else 0
    have hresidueSum : (∑ element : G, if (QuotientGroup.mk' subgroup) element = quotient then
        localResidue m hm ⟨coefficients element, hcoefficients.1 element⟩ else 0) =
        localResidue m hm (∑ element : G, localWeights element) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro element _
      by_cases hmember : (QuotientGroup.mk' subgroup) element = quotient <;>
        simp only [localWeights, hmember, ↓reduceIte, map_zero]
    rw [hresidueSum, localResidue_eq_zero_iff]
    have hcast : ((∑ element : G, localWeights element : localCoefficientSubring m hm) : ℂ) =
        ∑ element : G, if (QuotientGroup.mk' subgroup) element = quotient then coefficients element else 0 := by
      change (localCoefficientSubring m hm).subtype (∑ element : G, localWeights element) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro element _
      by_cases hmember : (QuotientGroup.mk' subgroup) element = quotient <;>
        simp only [localWeights, hmember, ↓reduceIte, Subring.coe_subtype, ZeroMemClass.coe_zero]
    rw [hcast]
    exact hsum quotient
  apply centralChar_residue_nilpotent m hm G hcharacter hcoefficients
  obtain ⟨exponent, hexponent⟩ := normalPSubgroup_quotient_kernel_nilpotent prime hprime
    (localResidueField m hm) G subgroup hpGroup
  refine ⟨exponent, ?_⟩
  have hpower := Ideal.pow_mem_pow (I := RingHom.ker
    (MonoidAlgebra.mapDomainAlgHom (localResidueField m hm) (localResidueField m hm)
      (QuotientGroup.mk' subgroup)).toRingHom) hkernel exponent
  rw [hexponent] at hpower
  exact hpower

end CFSG.BrauerThirdMainTheorem.Helpers
