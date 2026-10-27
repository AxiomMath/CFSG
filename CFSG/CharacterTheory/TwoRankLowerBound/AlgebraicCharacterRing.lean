module

public import CFSG.CharacterTheory.TwoRankLowerBound.ProductCharacterReconstruction
public import CFSG.CharacterTheory.TwoRankLowerBound.FiniteFunctionMaximalIdeal
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterValueIntegrality

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

universe groupUniverse

@[expose] def algebraicCharacterSpan (G : Type*) [Group G] : Submodule ComplexAlgebraicIntegers (G → ℂ) :=
  Submodule.span ComplexAlgebraicIntegers (virtualCharacters G : Set (G → ℂ))

theorem algebraicCharacterSpan_value_integral {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hmember : function ∈ algebraicCharacterSpan G) (element : G) :
    IsIntegral ℤ (function element) := by
  induction hmember using Submodule.span_induction with
  | mem character hvirtual => exact virtual_character_value_isIntegral character hvirtual element
  | zero => exact isIntegral_zero
  | add left right _ _ hleft hright => exact hleft.add hright
  | smul scalar function _ hintegral =>
    change IsIntegral ℤ ((scalar : ℂ) * function element)
    exact scalar.property.mul hintegral

theorem algebraicCharacterSpan_class {G : Type*} [Group G]
    (function : G → ℂ) (hmember : function ∈ algebraicCharacterSpan G) (element conjugator : G) :
    function (conjugator * element * conjugator⁻¹) = function element := by
  induction hmember using Submodule.span_induction with
  | mem character hvirtual => exact virtualCharacter_conjugation_invariant character hvirtual element conjugator
  | zero => rfl
  | add left right _ _ hleft hright => simp only [Pi.add_apply, hleft, hright]
  | smul scalar function _ hequal => simp only [Pi.smul_apply, hequal]

theorem algebraicCharacterSpan_mul {G : Type*} [Group G]
    (left right : G → ℂ) (hleft : left ∈ algebraicCharacterSpan G) (hright : right ∈ algebraicCharacterSpan G) :
    left * right ∈ algebraicCharacterSpan G := by
  induction hleft using Submodule.span_induction with
  | mem character hcharacter =>
    induction hright using Submodule.span_induction with
    | mem other hother => exact Submodule.subset_span (virtualCharacters_mul _ _ hcharacter hother)
    | zero => simpa only [mul_zero] using (algebraicCharacterSpan G).zero_mem
    | add first second _ _ hfirst hsecond =>
      rw [mul_add]
      exact (algebraicCharacterSpan G).add_mem hfirst hsecond
    | smul scalar function _ hfunction =>
      rw [mul_smul_comm]
      exact (algebraicCharacterSpan G).smul_mem scalar hfunction
  | zero => simpa only [zero_mul] using (algebraicCharacterSpan G).zero_mem
  | add first second _ _ hfirst hsecond =>
    rw [add_mul]
    exact (algebraicCharacterSpan G).add_mem hfirst hsecond
  | smul scalar function _ hfunction =>
    rw [smul_mul_assoc]
    exact (algebraicCharacterSpan G).smul_mem scalar hfunction

theorem algebraicCharacterSpan_one (G : Type groupUniverse) [Group G] :
    (1 : G → ℂ) ∈ algebraicCharacterSpan G := by
  apply Submodule.subset_span
  let data : FiniteComplexRepresentation.{groupUniverse, groupUniverse} G :=
    { vector := ULift.{groupUniverse} ℂ
      representation := Representation.trivial ℂ G (ULift.{groupUniverse} ℂ) }
  have hcharacter : data.character = 1 := by
    funext element
    change LinearMap.trace ℂ (ULift.{groupUniverse} ℂ) 1 = 1
    rw [LinearMap.trace_one, LinearEquiv.finrank_eq (ULift.moduleEquiv (R := ℂ) (M := ℂ))]
    simp
  rw [← hcharacter]
  exact character_mem_virtualCharacters data

@[expose] def algebraicCharacterRing (G : Type*) [Group G] : Subring (G → ComplexAlgebraicIntegers) where
  carrier := {function | (fun element => (function element : ℂ)) ∈ algebraicCharacterSpan G}
  zero_mem' := (algebraicCharacterSpan G).zero_mem
  one_mem' := algebraicCharacterSpan_one G
  add_mem' := by
    intro left right hleft hright
    exact (algebraicCharacterSpan G).add_mem hleft hright
  neg_mem' := by
    intro function hmember
    exact (algebraicCharacterSpan G).neg_mem hmember
  mul_mem' := by
    intro left right hleft hright
    exact algebraicCharacterSpan_mul _ _ hleft hright

theorem algebraicCharacterRing_constants {G : Type*} [Group G] (scalar : ComplexAlgebraicIntegers) :
    (fun _ : G => scalar) ∈ algebraicCharacterRing G := by
  change (fun _ : G => (scalar : ℂ)) ∈ algebraicCharacterSpan G
  have hscalar := (algebraicCharacterSpan G).smul_mem scalar (algebraicCharacterSpan_one G)
  have hequal : scalar • (1 : G → ℂ) = fun _ : G => (scalar : ℂ) := by
    funext element
    change (scalar : ℂ) * 1 = (scalar : ℂ)
    exact mul_one _
  rw [hequal] at hscalar
  exact hscalar

@[expose] noncomputable def algebraicCharacterFunction {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hmember : function ∈ algebraicCharacterSpan G) : G → ComplexAlgebraicIntegers :=
  fun element => ⟨function element, algebraicCharacterSpan_value_integral function hmember element⟩

theorem algebraicCharacterFunction_mem {G : Type*} [Group G] [Finite G]
    (function : G → ℂ) (hmember : function ∈ algebraicCharacterSpan G) :
    algebraicCharacterFunction function hmember ∈ algebraicCharacterRing G := hmember

theorem algebraicCharacterRing_maximal_evaluation {G : Type*} [Group G] [Fintype G]
    (ideal : Ideal (algebraicCharacterRing G)) [ideal.IsMaximal] :
    ∃ (element : G) (residueIdeal : Ideal ComplexAlgebraicIntegers), residueIdeal.IsMaximal ∧
      ideal = Ideal.comap (functionSubringEvaluation (algebraicCharacterRing G) element) residueIdeal :=
  finite_function_subring_maximal_ideal (algebraicCharacterRing G) algebraicCharacterRing_constants ideal

end CFSG.TwoRankLowerBound.Helpers
