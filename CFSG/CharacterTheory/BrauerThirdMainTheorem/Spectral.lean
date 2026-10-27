module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Convolution
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Idempotents
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

open CFSG
open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def coefficientAlgebra {G : Type*} [Group G] [Fintype G]
    (coefficients : G → ℂ) : MonoidAlgebra ℂ G :=
  ∑ element : G, MonoidAlgebra.single element (coefficients element)

theorem coefficientAlgebra_coeff {G : Type*} [Group G] [Fintype G]
    (coefficients : G → ℂ) (element : G) :
    (coefficientAlgebra coefficients).coeff element = coefficients element := by
  classical
  simp only [coefficientAlgebra, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  simp

theorem coefficientAlgebra_asAlgebraHom {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (coefficients : G → ℂ) :
    representation.asAlgebraHom (coefficientAlgebra coefficients) =
      coefficientOperator representation coefficients := by
  simp only [coefficientAlgebra, coefficientOperator, map_sum,
    Representation.asAlgebraHom_single]

theorem coefficientAlgebra_central {G : Type*} [Group G] [Fintype G]
    (coefficients : G → ℂ)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element)
    (algebraElement : MonoidAlgebra ℂ G) :
    algebraElement * coefficientAlgebra coefficients =
      coefficientAlgebra coefficients * algebraElement := by
  classical
  have hsingle (element : G) (scalar : ℂ) :
      MonoidAlgebra.single element scalar * coefficientAlgebra coefficients =
        coefficientAlgebra coefficients * MonoidAlgebra.single element scalar := by
    ext coefficient
    simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
      coefficientAlgebra_coeff]
    have hequal : coefficient * element⁻¹ =
        element * (element⁻¹ * coefficient) * element⁻¹ := by group
    rw [hequal, hcentral, mul_comm]
  have hsum : algebraElement =
      ∑ element : G, MonoidAlgebra.single element (algebraElement.coeff element) := by
    rw [← Finsupp.sum_fintype algebraElement.coeff MonoidAlgebra.single
      (fun _ => MonoidAlgebra.single_zero _)]
    exact (MonoidAlgebra.sum_coeff_single algebraElement).symm
  rw [hsum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun element _ => hsingle element _)

theorem centralChar_separates (G : Type) [Group G] [Finite G]
    (coefficients : G → ℂ)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element)
    (hvanishes : ∀ character ∈ BlocksIrr G, BlocksCentralChar character coefficients = 0) :
    coefficients = 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  let algebra := MonoidAlgebra ℂ G
  let centralElement := coefficientAlgebra coefficients
  let multiplication := LinearMap.mulRight algebra centralElement
  have hkernel : (⊤ : Submodule algebra algebra) ≤ multiplication.ker := by
    rw [← IsSemisimpleModule.sSup_simples_eq_top algebra algebra]
    apply sSup_le
    intro simpleModule hsimple
    change IsSimpleModule algebra simpleModule at hsimple
    let : IsSimpleModule algebra simpleModule := hsimple
    let representation := Representation.ofModule' (k := ℂ) (G := G) simpleModule
    have hirreducible : representation.IsIrreducible := ofModule'_isIrreducible
    let : representation.IsIrreducible := hirreducible
    have hcharacter : representation.character ∈ BlocksIrr G :=
      ⟨simpleModule, inferInstance, inferInstance, inferInstance,
        representation, hirreducible, rfl⟩
    have hoperator := coefficientOperator_scalar representation coefficients hcentral
    rw [hvanishes representation.character hcharacter, zero_smul] at hoperator
    intro vector hvector
    have haction := congrArg (fun operator : Module.End ℂ simpleModule =>
      operator ⟨vector, hvector⟩) hoperator
    rw [← coefficientAlgebra_asAlgebraHom, ofModule'_asAlgebraHom] at haction
    have hleft : centralElement * vector = 0 := by
      have hcoercion := congrArg (fun value : simpleModule => (value : algebra)) haction
      exact hcoercion
    rw [LinearMap.mem_ker]
    change vector * centralElement = 0
    rw [coefficientAlgebra_central coefficients hcentral]
    exact hleft
  have helement : centralElement = 0 := by
    have hone := hkernel (show (1 : algebra) ∈ (⊤ : Submodule algebra algebra) by trivial)
    simpa only [LinearMap.mem_ker, multiplication, LinearMap.mulRight_apply, one_mul] using hone
  funext element
  have hcoefficient := congrArg (fun value : algebra => value.coeff element) helement
  simpa only [centralElement, coefficientAlgebra_coeff, MonoidAlgebra.coeff_zero,
    Finsupp.zero_apply, Pi.zero_apply] using hcoefficient

noncomputable def spectralCoefficients (G : Type) [Group G] [Finite G]
    (eigenvalues : BlocksIrr G → ℂ) : G → ℂ :=
  ∑ᶠ character : BlocksIrr G,
    eigenvalues character • BlocksIdempotentCoeff G {(character : G → ℂ)}

theorem spectralCoefficients_eq_sum (G : Type) [Group G] [Finite G]
    [Fintype (BlocksIrr G)] (eigenvalues : BlocksIrr G → ℂ) :
    spectralCoefficients G eigenvalues = ∑ character : BlocksIrr G,
      eigenvalues character • BlocksIdempotentCoeff G {(character : G → ℂ)} := by
  exact finsum_eq_sum_of_fintype _

theorem spectralCoefficients_conj (G : Type) [Group G] [Finite G]
    (eigenvalues : BlocksIrr G → ℂ) (element conjugator : G) :
    spectralCoefficients G eigenvalues (conjugator * element * conjugator⁻¹) =
      spectralCoefficients G eigenvalues element := by
  let : Finite (BlocksIrr G) := (irr_linearIndependent G).finite
  let : Fintype (BlocksIrr G) := Fintype.ofFinite (BlocksIrr G)
  rw [spectralCoefficients_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro character _
  rw [idempotentCoeff_conj (Set.singleton_subset_iff.mpr character.property)]

theorem centralChar_spectralCoefficients (G : Type) [Group G] [Finite G]
    (eigenvalues : BlocksIrr G → ℂ) (character : BlocksIrr G) :
    BlocksCentralChar (character : G → ℂ) (spectralCoefficients G eigenvalues) =
      eigenvalues character := by
  let : Finite (BlocksIrr G) := (irr_linearIndependent G).finite
  let : Fintype (BlocksIrr G) := Fintype.ofFinite (BlocksIrr G)
  rw [spectralCoefficients_eq_sum, centralChar_sum]
  simp_rw [centralChar_smul]
  have hterm (candidate : BlocksIrr G) :
      eigenvalues candidate * BlocksCentralChar (character : G → ℂ)
        (BlocksIdempotentCoeff G {(candidate : G → ℂ)}) =
          if candidate = character then eigenvalues character else 0 := by
    rw [centralChar_idempotentCoeff (Set.singleton_subset_iff.mpr candidate.property)
      character.property]
    by_cases hequal : candidate = character
    · subst candidate
      simp
    · have hfunctions : (character : G → ℂ) ≠ (candidate : G → ℂ) := by
        intro hequalFunctions
        exact hequal (Subtype.ext hequalFunctions.symm)
      simp [hequal, hfunctions]
  simp_rw [hterm]
  simp

theorem central_spectral_expansion (G : Type) [Group G] [Finite G]
    (coefficients : G → ℂ)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element) :
    coefficients = spectralCoefficients G
      (fun character => BlocksCentralChar (character : G → ℂ) coefficients) := by
  apply sub_eq_zero.mp
  apply centralChar_separates G
  · intro element conjugator
    simp only [Pi.sub_apply, hcentral, spectralCoefficients_conj]
  · intro character hcharacter
    rw [centralChar_sub, centralChar_spectralCoefficients G _ ⟨character, hcharacter⟩]
    exact sub_self _

end CFSG.BrauerThirdMainTheorem.Helpers
