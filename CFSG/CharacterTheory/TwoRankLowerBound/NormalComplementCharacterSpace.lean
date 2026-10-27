module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionConvolution

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem normalSubgroupAverage_character_convolution {group : Type*}
    [Group group] [Fintype group] (subgroup : Subgroup group) [Fintype subgroup]
    (cardUnit : ℂˣ) (hcard : (cardUnit : ℂ) = Nat.card subgroup)
    (function : group → ℂ) (element : group)
    (hfixed : ∀ member : subgroup, function (element * member.val) = function element) :
    ∑ member : group, (normalSubgroupAverage subgroup cardUnit).coeff member *
      function (element * member) = function element := by
  change ∑ member : group,
    ((↑(cardUnit⁻¹) : ℂ) *
      (∑ element : subgroup, MonoidAlgebra.single element.val 1 : MonoidAlgebra ℂ group).coeff member) *
        function (element * member) = _
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ member : subgroup,
      (∑ argument : group,
        (↑(cardUnit⁻¹) : ℂ) * (MonoidAlgebra.single member.val 1).coeff argument *
          function (element * argument)) = (↑(cardUnit⁻¹) : ℂ) * function element := by
    intro member
    simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [Finset.sum_eq_single member.val]
    · simp only [ite_true, mul_one, hfixed]
    · intro argument _ hne
      simp only [ite_eq_right (Ne.symm hne), mul_zero, zero_mul]
    · simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    ← hcard, ← mul_assoc, Units.mul_inv, one_mul]

theorem normalSubgroupCharacterSupport_mem_of_right_invariant {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (subgroup : Subgroup group) [subgroup.Normal] [Fintype subgroup]
    (function : group → ℂ)
    (hclass : ∀ element conjugator, function (conjugator * element * conjugator⁻¹) = function element)
    (hfixed : ∀ element (member : subgroup), function (element * member.val) = function element) :
    function ∈ coefficientCharacterSpace basis (normalSubgroupCharacterSupport basis subgroup) := by
  let cardUnit : ℂˣ := Units.mk0 (Nat.card subgroup) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hequal : characterSubsetProjection basis (normalSubgroupCharacterSupport basis subgroup) function =
      function := by
    funext element
    rw [characterSubsetProjection_convolution basis _ function hclass,
      ← normalSubgroupAverage_eq_characterSubsetIdempotent basis subgroup cardUnit rfl]
    exact normalSubgroupAverage_character_convolution subgroup cardUnit rfl function element (hfixed element)
  rw [← hequal]
  exact characterSubsetProjection_mem basis _ function

theorem normalSubgroupCharacterSupport_right_invariant {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (subgroup : Subgroup group) (function : group → ℂ)
    (hfunction : function ∈ coefficientCharacterSpace basis (normalSubgroupCharacterSupport basis subgroup)) :
    ∀ element (member : subgroup), function (element * member.val) = function element := by
  induction hfunction using Submodule.span_induction with
  | mem generator hmember =>
    obtain ⟨label, hlabel, rfl⟩ := hmember
    have hkernel : ∀ member : subgroup, (basis.representation label).representation member.val = 1 := by
      simpa only [Finset.mem_coe, normalSubgroupCharacterSupport, Finset.mem_filter,
        Finset.mem_univ, true_and] using hlabel
    intro element member
    change LinearMap.trace ℂ (basis.representation label).vector
      ((basis.representation label).representation (element * member.val)) = _
    rw [map_mul, hkernel member, mul_one]
    rfl
  | zero => intros; rfl
  | add left right _ _ hleft hright =>
    intro element member
    simp only [Pi.add_apply, hleft, hright]
  | smul scalar function _ hequal =>
    intro element member
    simp only [Pi.smul_apply, hequal]

theorem normalComplement_principal_space_right_invariant {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) [IsLocalRing ring]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (quotient : group →* quotientGroup) (hsurjective : Function.Surjective quotient)
    (hquotient : IsPGroup prime quotientGroup) [Fintype quotient.ker]
    (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (function : group → ℂ)
    (hfunction : function ∈ coefficientCharacterSpace basis (coefficientBlock basis ring principal)) :
    ∀ element (member : quotient.ker), function (element * member.val) = function element := by
  rw [normalComplement_characterSupport_eq_block basis ring prime quotient hsurjective hquotient
    cardUnit hcard principal (normalSubgroupCharacterSupport_principal_mem basis quotient.ker principal hprincipal)]
      at hfunction
  exact normalSubgroupCharacterSupport_right_invariant basis quotient.ker function hfunction

theorem normalComplement_inflation_mem_principal_space {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (basis : FiniteIrreducibleCharacterBasis group) (ring : Subring ℂ) [IsLocalRing ring]
    (prime : ℕ) [Fact prime.Prime] [CharP (IsLocalRing.ResidueField ring) prime]
    (quotient : group →* quotientGroup) (hsurjective : Function.Surjective quotient)
    (hquotient : IsPGroup prime quotientGroup) [Fintype quotient.ker]
    (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (function : quotientGroup → ℂ)
    (hclass : ∀ element conjugator, function (conjugator * element * conjugator⁻¹) = function element) :
    function ∘ quotient ∈ coefficientCharacterSpace basis (coefficientBlock basis ring principal) := by
  rw [normalComplement_characterSupport_eq_block basis ring prime quotient hsurjective hquotient
    cardUnit hcard principal (normalSubgroupCharacterSupport_principal_mem basis quotient.ker principal hprincipal)]
  apply normalSubgroupCharacterSupport_mem_of_right_invariant
  · intro element conjugator
    simpa only [Function.comp_apply, map_mul, map_inv] using hclass (quotient element) (quotient conjugator)
  · intro element member
    simp only [Function.comp_apply, map_mul, MonoidHom.mem_ker.mp member.property, mul_one]

end CFSG.TwoRankLowerBound.Helpers
