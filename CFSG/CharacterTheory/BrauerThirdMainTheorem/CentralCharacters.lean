module

public import CFSG.CharacterTheory.Blocks.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def coefficientOperator {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (coefficients : G → ℂ) : Module.End ℂ space :=
  ∑ element : G, coefficients element • representation element

theorem coefficientOperator_intertwines {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (coefficients : G → ℂ)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element)
    (conjugator : G) :
    coefficientOperator representation coefficients ∘ₗ representation conjugator =
      representation conjugator ∘ₗ coefficientOperator representation coefficients := by
  classical
  unfold coefficientOperator
  ext vector
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul]
  apply Fintype.sum_equiv (MulAut.conj conjugator⁻¹).toEquiv
  intro element
  change coefficients element • ((representation element) ((representation conjugator) vector)) =
    coefficients (conjugator⁻¹ * element * (conjugator⁻¹)⁻¹) •
      ((representation conjugator)
        ((representation (conjugator⁻¹ * element * (conjugator⁻¹)⁻¹)) vector))
  rw [hcentral]
  congr 1
  have hproduct : representation element * representation conjugator =
      representation conjugator * representation (conjugator⁻¹ * element * (conjugator⁻¹)⁻¹) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  exact congrArg (fun operator : Module.End ℂ space => operator vector) hproduct

theorem coefficientOperator_trace {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) (coefficients : G → ℂ) :
    LinearMap.trace ℂ space (coefficientOperator representation coefficients) =
      ∑ element : G, coefficients element * representation.character element := by
  simp only [coefficientOperator, map_sum, map_smul, Representation.character, smul_eq_mul]

theorem coefficientOperator_scalar {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space] [FiniteDimensional ℂ space]
    (representation : Representation ℂ G space) [representation.IsIrreducible]
    (coefficients : G → ℂ)
    (hcentral : ∀ element conjugator : G,
      coefficients (conjugator * element * conjugator⁻¹) = coefficients element) :
    coefficientOperator representation coefficients =
      BlocksCentralChar representation.character coefficients • LinearMap.id := by
  classical
  let intertwiner : representation.IntertwiningMap representation := {
    toLinearMap := coefficientOperator representation coefficients
    isIntertwining' := coefficientOperator_intertwines representation coefficients hcentral
  }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  have hoperator : coefficientOperator representation coefficients = scalar • LinearMap.id := by
    have hmaps := congrArg Representation.IntertwiningMap.toLinearMap hscalar
    change scalar • LinearMap.id = coefficientOperator representation coefficients at hmaps
    exact hmaps.symm
  have : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  have : Nontrivial space := representation.asModuleEquiv.symm.toEquiv.nontrivial
  have hdegree : representation.character 1 ≠ 0 := by
    rw [Representation.char_one]
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := space)).ne'
  have htrace := congrArg (LinearMap.trace ℂ space) hoperator
  rw [coefficientOperator_trace, map_smul, LinearMap.trace_id,
    ← Representation.char_one representation, smul_eq_mul] at htrace
  have hcentralCharacter : BlocksCentralChar representation.character coefficients = scalar := by
    unfold BlocksCentralChar
    rw [finsum_eq_sum_of_fintype, htrace]
    exact mul_div_cancel_right₀ scalar hdegree
  rw [hcentralCharacter]
  exact hoperator

theorem ofModule'_asAlgebraHom {G : Type*} [Group G] {space : Type*}
    [AddCommGroup space] [Module ℂ space] [Module (MonoidAlgebra ℂ G) space]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) space] :
    (Representation.ofModule' (k := ℂ) (G := G) space).asAlgebraHom =
      Algebra.lsmul ℂ ℂ space := by
  rw [Representation.asAlgebraHom_def]
  exact (MonoidAlgebra.lift ℂ (Module.End ℂ space) G).apply_symm_apply _

theorem ofModule'_isIrreducible {G : Type*} [Group G] {space : Type*}
    [AddCommGroup space] [Module ℂ space] [Module (MonoidAlgebra ℂ G) space]
    [IsScalarTower ℂ (MonoidAlgebra ℂ G) space]
    [IsSimpleModule (MonoidAlgebra ℂ G) space] :
    (Representation.ofModule' (k := ℂ) (G := G) space).IsIrreducible := by
  let representation := Representation.ofModule' (k := ℂ) (G := G) space
  let equivalence : representation.asModule ≃ₗ[MonoidAlgebra ℂ G] space := {
    __ := representation.asModuleEquiv.toAddEquiv
    map_smul' coefficient vector := by
      change representation.asModuleEquiv (coefficient • vector) =
        coefficient • representation.asModuleEquiv vector
      rw [representation.asModuleEquiv_map_smul, ofModule'_asAlgebraHom]
      rfl
  }
  exact (representation.irreducible_iff_isSimpleModule_asModule).mpr
    (IsSimpleModule.congr equivalence)

end CFSG.BrauerThirdMainTheorem.Helpers
