module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Convolution
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralChar_integral_coefficients {G : Type*} [Group G] [Finite G]
    {character coefficients : G → ℂ} (hcharacter : character ∈ BlocksIrr G)
    (hcoefficients : ∀ element, coefficients element ∈ BlocksAlgInt)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element) :
    IsIntegral ℤ (BlocksCentralChar character coefficients) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨space, _, _, _, representation, hirreducible, rfl⟩ := hcharacter
  let : representation.IsIrreducible := hirreducible
  let integerElement : MonoidAlgebra BlocksAlgInt G :=
    ∑ element : G, MonoidAlgebra.single element ⟨coefficients element, hcoefficients element⟩
  have : Algebra.IsIntegral ℤ BlocksAlgInt :=
    IsIntegralClosure.isIntegral_algebra ℤ ℂ
  have hintegerElement : IsIntegral ℤ integerElement :=
    isIntegral_trans (R := ℤ) (A := BlocksAlgInt) integerElement
      (Algebra.IsIntegral.isIntegral (R := BlocksAlgInt) integerElement)
  let coefficientMap := MonoidAlgebra.mapRingHom G BlocksAlgInt.val.toRingHom
  let actionMap := representation.asAlgebraHom.toRingHom.comp coefficientMap
  have hoperatorIntegral : IsIntegral ℤ (actionMap integerElement) := by
    apply IsIntegral.map_of_comp_eq (RingHom.id ℤ) actionMap
    · ext integer
      simp
    · exact hintegerElement
  have hoperator : actionMap integerElement = coefficientOperator representation coefficients := by
    simp only [actionMap, coefficientMap, integerElement, RingHom.comp_apply, map_sum,
      MonoidAlgebra.mapRingHom_single, coefficientOperator]
    apply Finset.sum_congr rfl
    intro element _
    change representation.asAlgebraHom (MonoidAlgebra.single element (coefficients element)) = _
    exact Representation.asAlgebraHom_single representation element (coefficients element)
  rw [hoperator, coefficientOperator_scalar representation coefficients hcentral] at hoperatorIntegral
  have : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  have : Nontrivial space := representation.asModuleEquiv.symm.toEquiv.nontrivial
  apply (isIntegral_algebraMap_iff (R := ℤ) (A := ℂ) (B := Module.End ℂ space)).mp
  exact hoperatorIntegral

theorem centralChar_localRing {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {character coefficients : G → ℂ} (hcharacter : character ∈ BlocksIrr G)
    (hcoefficients : BlocksIsCentralR m coefficients) :
    BlocksCentralChar character coefficients ∈ BlocksLocalRing m := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨denominator, hdenominator, hvalues⟩ := common_denominator m hm Finset.univ
    coefficients (fun entry _ => hcoefficients.1 entry)
  let scaled : G → ℂ := (denominator : ℂ) • coefficients
  have hscaled : ∀ element, scaled element ∈ BlocksAlgInt := by
    intro element
    obtain ⟨numerator, hnumerator⟩ := hvalues element (Finset.mem_univ element)
    change (denominator : ℂ) * coefficients element ∈ BlocksAlgInt
    rw [← hnumerator]
    exact numerator.property
  have hscaledCentral : ∀ element conjugator : G,
      scaled (conjugator * element * conjugator⁻¹) = scaled element := by
    intro element conjugator
    change (denominator : ℂ) * coefficients (conjugator * element * conjugator⁻¹) =
      (denominator : ℂ) * coefficients element
    rw [hcoefficients.2]
  have hintegral := centralChar_integral_coefficients hcharacter hscaled hscaledCentral
  let numerator : BlocksAlgInt := ⟨BlocksCentralChar character scaled,
    (mem_integralClosure_iff ℤ ℂ).mpr hintegral⟩
  refine ⟨numerator, denominator, hdenominator, ?_⟩
  change BlocksCentralChar character coefficients =
    BlocksCentralChar character ((denominator : ℂ) • coefficients) / (denominator : ℂ)
  rw [centralChar_smul, mul_div_cancel_left₀ _ (denominator_ne_zero m hdenominator)]

end CFSG.BrauerThirdMainTheorem.Helpers
