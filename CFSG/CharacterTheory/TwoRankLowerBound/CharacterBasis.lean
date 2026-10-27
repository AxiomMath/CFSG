module

public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterExpansion
public import CFSG.CharacterTheory.TwoRankLowerBound.WeightedCharacterOperator

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

attribute [local instance] RestrictScalars.module

universe groupUniverse

set_option backward.isDefEq.respectTransparency false in
theorem weightedCharacterOperator_zero_of_decomposition {G vector : Type*} [Group G] [Fintype G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) {size : ℕ}
    (summand : Fin size → Submodule (MonoidAlgebra ℂ G) representation.asModule)
    (equivalence : representation.asModule ≃ₗ[MonoidAlgebra ℂ G]
      (∀ label : Fin size, summand label)) (function : G → ℂ)
    (hzero : ∀ label, weightedCharacterOperator
      (Representation.ofModule (k := ℂ) (G := G) (summand label)) function = 0) :
    weightedCharacterOperator representation function = 0 := by
  let : Module.Finite ℂ representation.asModule :=
    Module.Finite.equiv representation.asModuleEquiv.symm
  let : ∀ label : Fin size, FiniteDimensional ℂ (summand label) := fun label =>
    Module.Finite.of_injective ((summand label).subtype.restrictScalars ℂ)
      (summand label).subtype_injective
  let transport : vector ≃ₗ[ℂ] (∀ label : Fin size, summand label) :=
    representation.asModuleEquiv.symm.trans (equivalence.restrictScalars ℂ)
  have haction : ∀ element vectorValue label,
      transport (representation element vectorValue) label =
        MonoidAlgebra.of ℂ G element • transport vectorValue label := by
    intro element vectorValue label
    change equivalence (representation.asModuleEquiv.symm (representation element vectorValue)) label = _
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul]
    rfl
  apply LinearMap.ext
  intro vectorValue
  apply transport.injective
  apply funext
  intro label
  let scalarTransport := restrictScalarsLinearEquiv (G := G) (module := summand label)
  have heval := congrArg
    (fun operator => scalarTransport (operator (scalarTransport.symm (transport vectorValue label))))
    (hzero label)
  have hcomponent : ∀ element,
      scalarTransport ((Representation.ofModule (k := ℂ) (G := G) (summand label) element)
        (scalarTransport.symm (transport vectorValue label))) =
      MonoidAlgebra.of ℂ G element • transport vectorValue label := by
    intro element
    rfl
  simp only [weightedCharacterOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, hcomponent, LinearMap.zero_apply, map_zero] at heval
  simpa only [weightedCharacterOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, haction,
    LinearMap.zero_apply, map_zero, Pi.zero_apply] using heval

theorem leftRegular_weightedCharacterOperator_faithful {G : Type*} [Group G] [Fintype G]
    (function : G → ℂ)
    (hzero : weightedCharacterOperator (Representation.leftRegular ℂ G) function = 0) :
    function = 0 := by
  have heval := congrArg (fun operator => operator (MonoidAlgebra.single 1 1)) hzero
  have haction : ∀ element : G,
      Representation.leftRegular ℂ G element (MonoidAlgebra.single 1 1) =
      MonoidAlgebra.single element 1 := by
    intro element
    change Representation.ofMulAction ℂ G G element (MonoidAlgebra.single 1 1) = _
    rw [Representation.ofMulAction_single]
    simp
  simp only [weightedCharacterOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    haction, LinearMap.zero_apply] at heval
  ext element
  have hcoefficient := congrArg (fun value : MonoidAlgebra ℂ G => value.coeff element⁻¹) heval
  simpa only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, inv_inv,
    MonoidAlgebra.coeff_zero, Finsupp.zero_apply, Pi.zero_apply]
    using hcoefficient

set_option backward.isDefEq.respectTransparency false in
theorem finite_irreducible_character_separating_family {G : Type groupUniverse} [Group G] [Fintype G] :
    ∃ (size : ℕ) (representation : Fin size → FiniteComplexRepresentation.{groupUniverse, groupUniverse} G),
      (∀ label, (representation label).IsIrreducible) ∧
      ∀ function : G → ℂ,
        (∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element) →
        (∀ label, characterPairing function (representation label).character = 0) → function = 0 := by
  let regular := Representation.leftRegular ℂ G
  obtain ⟨size, summand, equivalence, hsimple⟩ :=
    representation_exists_simple_module_decomposition regular
  let : Module.Finite ℂ regular.asModule := Module.Finite.equiv regular.asModuleEquiv.symm
  let : ∀ label : Fin size, FiniteDimensional ℂ (summand label) := fun label =>
    Module.Finite.of_injective ((summand label).subtype.restrictScalars ℂ)
      (summand label).subtype_injective
  let representation := fun label : Fin size =>
    moduleFiniteComplexRepresentation (G := G) (module := summand label)
  have hirreducible : ∀ label, (representation label).IsIrreducible := by
    intro label
    let : IsSimpleModule (MonoidAlgebra ℂ G) (summand label) := hsimple label
    exact moduleFiniteComplexRepresentation_isIrreducible
  refine ⟨size, representation, hirreducible, ?_⟩
  intro function hclass hpair
  apply leftRegular_weightedCharacterOperator_faithful
  apply weightedCharacterOperator_zero_of_decomposition regular summand equivalence function
  intro label
  exact irreducible_weightedCharacterOperator_zero (representation label) (hirreducible label)
    function hclass (hpair label)

structure FiniteIrreducibleCharacterBasis (G : Type groupUniverse) [Group G] [Fintype G] where
  index : Type groupUniverse
  [fintype : Fintype index]
  representation : index → FiniteComplexRepresentation.{groupUniverse, groupUniverse} G
  irreducible : ∀ label, (representation label).IsIrreducible
  distinct : Function.Injective (fun label => (representation label).character)
  separates : ∀ function : G → ℂ,
    (∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element) →
    (∀ label, characterPairing function (representation label).character = 0) → function = 0

attribute [instance] FiniteIrreducibleCharacterBasis.fintype

theorem finiteIrreducibleCharacterBasis_exists {G : Type groupUniverse} [Group G] [Fintype G] :
    Nonempty (FiniteIrreducibleCharacterBasis G) := by
  obtain ⟨size, representation, hirreducible, hseparates⟩ :=
    finite_irreducible_character_separating_family (G := G)
  let support : Finset (G → ℂ) := Finset.univ.image (fun label => (representation label).character)
  have hmember : ∀ character : support,
      ∃ label : Fin size, (representation label).character = character := by
    intro character
    obtain ⟨label, _, hequal⟩ := Finset.mem_image.mp character.property
    exact ⟨label, hequal⟩
  choose label hlabel using hmember
  refine ⟨{
    index := support
    representation := fun character => representation (label character)
    irreducible := fun character => hirreducible (label character)
    distinct := ?_
    separates := ?_ }⟩
  · intro left right hequal
    apply Subtype.ext
    exact (hlabel left).symm.trans (hequal.trans (hlabel right))
  · intro function hclass hpair
    apply hseparates function hclass
    intro original
    let character : support := ⟨(representation original).character,
      Finset.mem_image.mpr ⟨original, Finset.mem_univ _, rfl⟩⟩
    have hzero := hpair character
    simpa only [hlabel character] using hzero

theorem characterPairing_sub_left {G : Type*} [Group G] [Fintype G]
    (left right character : G → ℂ) :
    characterPairing (left - right) character =
      characterPairing left character - characterPairing right character := by
  simp only [characterPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem finiteIrreducibleCharacterBasis_reconstruction {G : Type groupUniverse} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (function : G → ℂ)
    (hclass : ∀ element conjugator : G, function (conjugator * element * conjugator⁻¹) = function element)
    (element : G) : function element =
      ∑ label, characterPairing function (basis.representation label).character *
        (basis.representation label).character element := by
  let expansion : G → ℂ := fun member =>
    ∑ label, characterPairing function (basis.representation label).character *
      (basis.representation label).character member
  have hzero : function - expansion = 0 := by
    apply basis.separates
    · intro member conjugator
      simp only [Pi.sub_apply, expansion, hclass]
      congr 1
      apply Finset.sum_congr rfl
      intro label _
      rw [FiniteComplexRepresentation.character, Representation.char_conj]
    · intro label
      rw [characterPairing_sub_left]
      have hcoefficient := characterPairing_distinct_expansion_coefficient basis.representation
        basis.irreducible basis.distinct
        (fun label => characterPairing function (basis.representation label).character) label
      change characterPairing function (basis.representation label).character -
        characterPairing expansion (basis.representation label).character = 0
      rw [hcoefficient, sub_self]
  exact sub_eq_zero.mp (congrFun hzero element)

end CFSG.TwoRankLowerBound.Helpers
