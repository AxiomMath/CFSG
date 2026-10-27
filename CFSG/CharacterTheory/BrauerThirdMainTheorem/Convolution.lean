module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralCharacters
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalRing
public import Mathlib.RingTheory.PiTensorProduct

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def coefficientConvolution {G : Type*} [Group G] [Finite G]
    (left right : G → ℂ) : G → ℂ :=
  fun element => ∑ᶠ factor : G, left factor * right (factor⁻¹ * element)

theorem coefficientConvolution_apply {G : Type*} [Group G] [Fintype G]
    (left right : G → ℂ) (element : G) :
    coefficientConvolution left right element =
      ∑ factor : G, left factor * right (factor⁻¹ * element) := by
  exact finsum_eq_sum_of_fintype _

theorem coefficientConvolution_local {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : G → ℂ}
    (hleft : ∀ element, left element ∈ BlocksLocalRing m)
    (hright : ∀ element, right element ∈ BlocksLocalRing m) :
    ∀ element, coefficientConvolution left right element ∈ BlocksLocalRing m := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro element
  rw [coefficientConvolution_apply]
  apply localRing_sum m hm
  intro factor _
  exact localRing_mul m hm (hleft factor) (hright (factor⁻¹ * element))

theorem coefficientConvolution_central {G : Type*} [Group G] [Finite G]
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) {left right : G → ℂ}
    (hleft : BlocksIsCentralR m left) (hright : BlocksIsCentralR m right) :
    BlocksIsCentralR m (coefficientConvolution left right) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  constructor
  · intro element
    rw [coefficientConvolution_apply]
    apply localRing_sum m hm
    intro factor _
    exact localRing_mul m hm (hleft.1 factor) (hright.1 (factor⁻¹ * element))
  · intro element conjugator
    rw [coefficientConvolution_apply, coefficientConvolution_apply]
    apply Fintype.sum_equiv (MulAut.conj conjugator⁻¹).toEquiv
    intro factor
    change left factor * right (factor⁻¹ * (conjugator * element * conjugator⁻¹)) =
      left (conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹) *
        right ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element)
    rw [hleft.2]
    congr 1
    have hequal : factor⁻¹ * (conjugator * element * conjugator⁻¹) =
        conjugator * ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element) *
          conjugator⁻¹ := by group
    rw [hequal, hright.2]

theorem coefficientOperator_convolution {G : Type*} [Group G] [Fintype G]
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    (representation : Representation ℂ G space) (left right : G → ℂ) :
    coefficientOperator representation (coefficientConvolution left right) =
      coefficientOperator representation left * coefficientOperator representation right := by
  classical
  unfold coefficientOperator
  simp only [coefficientConvolution_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, smul_mul_smul]
  apply Finset.sum_congr rfl
  intro factor _
  apply Fintype.sum_equiv (Equiv.mulLeft factor⁻¹)
  intro element
  change (left factor * right (factor⁻¹ * element)) • representation element =
    (left factor * right (factor⁻¹ * element)) •
      (representation factor * representation (factor⁻¹ * element))
  rw [← map_mul, mul_inv_cancel_left]

theorem centralChar_add {G : Type*} [Group G] [Finite G]
    (character left right : G → ℂ) :
    BlocksCentralChar character (left + right) =
      BlocksCentralChar character left + BlocksCentralChar character right := by
  classical
  let : Fintype G := Fintype.ofFinite G
  simp only [BlocksCentralChar, finsum_eq_sum_of_fintype, Pi.add_apply, add_mul,
    Finset.sum_add_distrib, add_div]

theorem centralChar_smul {G : Type*} [Group G] [Finite G]
    (character coefficients : G → ℂ) (scalar : ℂ) :
    BlocksCentralChar character (scalar • coefficients) =
      scalar * BlocksCentralChar character coefficients := by
  classical
  let : Fintype G := Fintype.ofFinite G
  simp only [BlocksCentralChar, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul,
    mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem centralChar_zero {G : Type*} [Group G] (character : G → ℂ) :
    BlocksCentralChar character 0 = 0 := by
  simp only [BlocksCentralChar, Pi.zero_apply, zero_mul, finsum_zero, zero_div]

theorem centralChar_sub {G : Type*} [Group G] [Finite G]
    (character left right : G → ℂ) :
    BlocksCentralChar character (left - right) =
      BlocksCentralChar character left - BlocksCentralChar character right := by
  classical
  let : Fintype G := Fintype.ofFinite G
  simp only [BlocksCentralChar, finsum_eq_sum_of_fintype, Pi.sub_apply, sub_mul,
    Finset.sum_sub_distrib, sub_div]

theorem centralChar_sum {G : Type*} [Group G] [Finite G] {index : Type*}
    (character : G → ℂ) (indices : Finset index) (coefficients : index → G → ℂ) :
    BlocksCentralChar character (∑ entry ∈ indices, coefficients entry) =
      ∑ entry ∈ indices, BlocksCentralChar character (coefficients entry) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, centralChar_zero]
  | @insert entry indices hentry hinduction =>
      rw [Finset.sum_insert hentry, Finset.sum_insert hentry, centralChar_add, hinduction]

theorem centralChar_convolution {G : Type*} [Group G] [Finite G]
    {character : G → ℂ} (hcharacter : character ∈ BlocksIrr G) (left right : G → ℂ)
    (hleft : ∀ element conjugator : G, left (conjugator * element * conjugator⁻¹) = left element)
    (hright : ∀ element conjugator : G, right (conjugator * element * conjugator⁻¹) = right element) :
    BlocksCentralChar character (coefficientConvolution left right) =
      BlocksCentralChar character left * BlocksCentralChar character right := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨space, _, _, _, representation, hirreducible, rfl⟩ := hcharacter
  let : representation.IsIrreducible := hirreducible
  have hconvolutionCentral : ∀ element conjugator : G,
      coefficientConvolution left right (conjugator * element * conjugator⁻¹) =
        coefficientConvolution left right element := by
    intro element conjugator
    rw [coefficientConvolution_apply, coefficientConvolution_apply]
    apply Fintype.sum_equiv (MulAut.conj conjugator⁻¹).toEquiv
    intro factor
    change left factor * right (factor⁻¹ * (conjugator * element * conjugator⁻¹)) =
      left (conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹) *
        right ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element)
    rw [hleft]
    congr 1
    have hequal : factor⁻¹ * (conjugator * element * conjugator⁻¹) =
        conjugator * ((conjugator⁻¹ * factor * (conjugator⁻¹)⁻¹)⁻¹ * element) *
          conjugator⁻¹ := by group
    rw [hequal, hright]
  have hoperators := coefficientOperator_convolution representation left right
  rw [coefficientOperator_scalar representation _ hconvolutionCentral,
    coefficientOperator_scalar representation _ hleft,
    coefficientOperator_scalar representation _ hright] at hoperators
  have : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  have : Nontrivial space := representation.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨vector, hvector⟩ := exists_ne (0 : space)
  have hvalues := congrArg (fun operator : Module.End ℂ space => operator vector) hoperators
  simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_smul] at hvalues
  exact (smul_left_inj hvector).mp hvalues

end CFSG.BrauerThirdMainTheorem.Helpers
