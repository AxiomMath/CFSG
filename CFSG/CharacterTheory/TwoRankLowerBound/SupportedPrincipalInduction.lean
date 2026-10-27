module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterSubsetLattices
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionPairing
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalLocalSectionProjection

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside {group : Type*}
    [Group group] [Fintype group] (basis : FiniteIrreducibleCharacterBasis group)
    (support : Finset basis.index) (function : group → ℂ) :
    function ∈ coefficientCharacterSpace basis support ↔
      (∀ element conjugator, function (conjugator * element * conjugator⁻¹) = function element) ∧
      ∀ label, label ∉ support →
        characterPairing function (basis.representation label).character = 0 := by
  constructor
  · intro hfunction
    constructor
    · induction hfunction using Submodule.span_induction with
      | mem generator hmember =>
        obtain ⟨label, _, rfl⟩ := hmember
        intro element conjugator
        exact Representation.char_conj _ _ _
      | zero => intros; rfl
      | add left right _ _ hleft hright =>
        intro element conjugator
        simp only [Pi.add_apply, hleft, hright]
      | smul scalar function _ hequal =>
        intro element conjugator
        simp only [Pi.smul_apply, hequal]
    · exact coefficientCharacterSpace_pairing_zero_outside basis support function hfunction
  · rintro ⟨hclass, hzero⟩
    have hexpansion : function = ∑ label : basis.index,
        characterPairing function (basis.representation label).character •
          (basis.representation label).character := by
      funext element
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
        finiteIrreducibleCharacterBasis_reconstruction basis function hclass element
    rw [hexpansion]
    apply Submodule.sum_mem
    intro label _
    by_cases hlabel : label ∈ support
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨label, hlabel, rfl⟩)
    · rw [hzero label hlabel, zero_smul]
      exact (coefficientCharacterSpace basis support).zero_mem

theorem supported_inducedFunction_mem_coefficientCharacterSpace {group : Type*}
    [Group group] [Fintype group] (subgroup : Subgroup group)
    (basis : FiniteIrreducibleCharacterBasis group) (support : Finset basis.index)
    (localBasis : FiniteIrreducibleCharacterBasis subgroup) (localSupport : Finset localBasis.index)
    (domain : Set subgroup) (function : subgroup → ℂ)
    (hspace : function ∈ coefficientCharacterSpace localBasis localSupport)
    (hsupport : ∀ element, element ∉ domain → function element = 0)
    (hzero : ∀ label, label ∉ support → ∀ element, element ∈ domain →
      characterSubsetProjection localBasis localSupport
        (fun member => (basis.representation label).character member.val) element⁻¹ = 0) :
    inducedFunction subgroup function ∈ coefficientCharacterSpace basis support := by
  apply (coefficientCharacterSpace_mem_iff_class_and_pairing_zero_outside basis support _).mpr
  refine ⟨inducedFunction_conjugate subgroup function, ?_⟩
  intro label hlabel
  rw [characterPairing_inducedFunction_left subgroup function _
    (fun element conjugator => Representation.char_conj _ _ _)]
  exact coefficientCharacterSpace_pairing_zero_of_projected_inverse_support
    localBasis localSupport domain function _ hspace hsupport (hzero label hlabel)

theorem supported_local_principal_section_induced_mem {group quotientGroup : Type*}
    [Group group] [Fintype group] [Group quotientGroup] [Finite quotientGroup]
    (ring : Subring ℂ) [IsLocalRing ring] (prime : ℕ) [Fact prime.Prime]
    [CharP (IsLocalRing.ResidueField ring) prime]
    (basis : FiniteIrreducibleCharacterBasis group) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (primary : group) (exponent : ℕ) (hprimary : orderOf primary ∣ prime ^ exponent)
    (localBasis : FiniteIrreducibleCharacterBasis
      (Subgroup.centralizer (Subgroup.zpowers primary : Set group)))
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (quotient : Subgroup.centralizer (Subgroup.zpowers primary : Set group) →* quotientGroup)
    (hsurjective : Function.Surjective quotient) (hquotient : IsPGroup prime quotientGroup)
    [Fintype quotient.ker] (cardUnit : ringˣ) (hcard : (cardUnit : ring) = Nat.card quotient.ker)
    (hroots : ∀ period : ℕ, 0 < period → ∀ root : ℂ, root ^ period = 1 → root ∈ ring)
    (function : Subgroup.centralizer (Subgroup.zpowers primary : Set group) → ℂ)
    (hspace : function ∈ coefficientCharacterSpace localBasis (coefficientBlock localBasis ring localPrincipal))
    (hsupport : ∀ element, function element ≠ 0 →
      ∃ regular : Subgroup.centralizer (Subgroup.zpowers primary : Set group),
        Nat.Coprime prime (orderOf regular.val) ∧
          element = (⟨primary, element_mem_centralizer_zpowers primary⟩ :
            Subgroup.centralizer (Subgroup.zpowers primary : Set group)) * regular) :
    inducedFunction (Subgroup.centralizer (Subgroup.zpowers primary : Set group)) function ∈
      coefficientCharacterSpace basis (coefficientBlock basis ring principal) := by
  apply supported_inducedFunction_mem_coefficientCharacterSpace _ basis _ localBasis _
    {element | function element ≠ 0} function hspace
  · intro element hzero
    simpa only [Set.mem_ofPred_eq, not_not] using hzero
  · intro label hlabel element helement
    obtain ⟨regular, hregular, rfl⟩ := hsupport element helement
    have hnotPrincipal : principal ∉ coefficientBlock basis ring label := by
      intro hmember
      have hblocks := coefficientBlock_eq_of_mem basis ring hmember
      have hself := coefficientBlock_self_mem basis ring label
      rw [← hblocks] at hself
      exact hlabel hself
    exact nonprincipal_admissible_local_principal_section_zero ring prime basis
      (coefficientBlock basis ring label) (coefficientBlock_admissible basis ring label)
      principal hprincipal hnotPrincipal primary exponent hprimary localBasis localPrincipal
      hlocalPrincipal quotient hsurjective hquotient cardUnit hcard regular hregular hroots label
      (coefficientBlock_self_mem basis ring label)

end CFSG.TwoRankLowerBound.Helpers
