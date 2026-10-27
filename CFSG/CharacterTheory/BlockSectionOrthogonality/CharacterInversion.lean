module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open CFSG
namespace CFSG.BlockSectionOrthogonality.Helpers

open scoped ComplexOrder

theorem representation_matrix_character_inversion {G : Type*} [Group G] [Fintype G]
    {index : Type*} [Fintype index] [DecidableEq index]
    (representation : G →* Matrix index index ℂ) (element : G) :
    (representation element⁻¹).trace = starRingEnd ℂ (representation element).trace := by
  classical
  let gram : Matrix index index ℂ :=
    ∑ index, (representation index).conjTranspose * representation index
  have hGramPositive : gram.PosDef := by
    apply Matrix.posDef_sum Finset.univ_nonempty
    intro groupElement hIndex
    have hInjective : Function.Injective (representation groupElement).mulVec := by
      intro left right hEqual
      have := congrArg (fun vector => (representation groupElement⁻¹).mulVec vector) hEqual
      simpa only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel,
        map_one, Matrix.one_mulVec] using this
    simpa only [mul_one] using
      (Matrix.PosDef.one (R := ℂ) (n := index)).conjTranspose_mul_mul_same hInjective
  have hGramUnit := hGramPositive.isUnit
  have hInvariant : (representation element).conjTranspose * gram * representation element = gram := by
    have hReindex := Equiv.sum_comp (Equiv.mulRight element)
      (fun index => (representation index).conjTranspose * representation index)
    dsimp [gram]
    rw [Finset.mul_sum, Finset.sum_mul]
    rw [← hReindex]
    apply Finset.sum_congr rfl
    intro index hIndex
    change _ = (representation (index * element)).conjTranspose * representation (index * element)
    rw [map_mul, Matrix.conjTranspose_mul]
    simp only [mul_assoc]
  have hAdjoint : (representation element).conjTranspose * gram = gram * representation element⁻¹ := by
    have hMultiply := congrArg (fun matrix => matrix * representation element⁻¹) hInvariant
    simpa only [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] using hMultiply
  let gramUnit := hGramUnit.unit
  have hGramUnitVal : (gramUnit : Matrix index index ℂ) = gram := hGramUnit.unit_spec
  have hConjugate : representation element⁻¹ =
      (↑gramUnit⁻¹ : Matrix index index ℂ) * (representation element).conjTranspose *
        (gramUnit : Matrix index index ℂ) := by
    rw [hGramUnitVal, mul_assoc, hAdjoint, ← mul_assoc, ← hGramUnitVal,
      Units.inv_mul, one_mul]
  rw [hConjugate, Matrix.trace_mul_cycle, Units.mul_inv, one_mul,
    Matrix.trace_conjTranspose]
  rfl

theorem representation_character_inversion {G : Type*} [Group G] [Finite G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) (element : G) :
    representation.character element⁻¹ = starRingEnd ℂ (representation.character element) := by
  classical
  let := Fintype.ofFinite G
  let basis := Module.finBasis ℂ space
  let matrixRepresentation : G →* Matrix (Fin (Module.finrank ℂ space))
      (Fin (Module.finrank ℂ space)) ℂ :=
    (LinearMap.toMatrixAlgEquiv basis).toMonoidHom.comp representation
  have hMatrix := representation_matrix_character_inversion matrixRepresentation element
  change (LinearMap.toMatrix basis basis (representation element⁻¹)).trace =
    starRingEnd ℂ (LinearMap.toMatrix basis basis (representation element)).trace at hMatrix
  simpa only [Representation.character, ← LinearMap.trace_eq_matrix_trace] using hMatrix

theorem irreducible_character_inversion {G : Type*} [Group G] [Finite G]
    {character : G → ℂ} (hCharacter : character ∈ BlocksIrr G) (element : G) :
    character element⁻¹ = starRingEnd ℂ (character element) := by
  rcases hCharacter with ⟨space, hAdd, hModule, hFinite, representation, hIrr, rfl⟩
  exact representation_character_inversion representation element

end CFSG.BlockSectionOrthogonality.Helpers
