module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.LocalGroupAlgebra
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ResidueExtension
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem groupAlgebra_center_coeff_conj (ring : Type*) [CommRing ring]
    (G : Type*) [Group G] {value : MonoidAlgebra ring G}
    (hvalue : value ∈ Subalgebra.center ring (MonoidAlgebra ring G)) (element conjugator : G) :
    value.coeff (conjugator * element * conjugator⁻¹) = value.coeff element := by
  have hcomm := (Subalgebra.mem_center_iff.mp hvalue) (MonoidAlgebra.single conjugator 1)
  have hcoeff := congrArg (fun algebraValue : MonoidAlgebra ring G =>
    algebraValue.coeff (conjugator * element)) hcomm
  rw [MonoidAlgebra.coeff_single_mul_mul, one_mul] at hcoeff
  have hright : (value * MonoidAlgebra.single conjugator 1).coeff (conjugator * element) =
      value.coeff (conjugator * element * conjugator⁻¹) := by
    have hequal := MonoidAlgebra.coeff_mul_single_mul value 1 conjugator
      (conjugator * element * conjugator⁻¹)
    simpa only [mul_inv_cancel_right, inv_mul_cancel_right, mul_one] using hequal
  rw [hright] at hcoeff
  exact hcoeff.symm

theorem groupAlgebra_mem_center_of_coeff_conj (ring : Type*) [CommRing ring]
    (G : Type*) [Group G] {value : MonoidAlgebra ring G}
    (hvalue : ∀ element conjugator : G,
      value.coeff (conjugator * element * conjugator⁻¹) = value.coeff element) :
    value ∈ Subalgebra.center ring (MonoidAlgebra ring G) := by
  classical
  apply Subalgebra.mem_center_iff.mpr
  intro other
  induction other using MonoidAlgebra.induction_on with
  | of element =>
      apply MonoidAlgebra.ext
      apply Finsupp.ext
      intro factor
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one]
      have hequal : element * (element⁻¹ * factor) * element⁻¹ = factor * element⁻¹ := by group
      exact (hequal ▸ hvalue (element⁻¹ * factor) element).symm
  | add left right hleft hright =>
      rw [add_mul, mul_add, hleft, hright]
  | smul scalar other hother =>
      rw [smul_mul_assoc, mul_smul_comm, hother]

@[expose] noncomputable def centralLocalCoefficients (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G]
    (value : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) : G → ℂ :=
  fun element => (value.val.coeff element : ℂ)

theorem centralLocalCoefficients_central (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G]
    (value : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) :
    BlocksIsCentralR m (centralLocalCoefficients m hm G value) := by
  constructor
  · intro element
    exact (value.val.coeff element).property
  · intro element conjugator
    exact congrArg Subtype.val (groupAlgebra_center_coeff_conj _ G value.property element conjugator)

theorem centralLocalCoefficients_add (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G]
    (left right : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) :
    centralLocalCoefficients m hm G (left + right) =
      centralLocalCoefficients m hm G left + centralLocalCoefficients m hm G right := by
  ext element
  simp only [centralLocalCoefficients, Subalgebra.coe_add, MonoidAlgebra.coeff_add,
    Finsupp.add_apply, Subring.coe_add, Pi.add_apply]

theorem centralLocalCoefficients_one (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] :
    centralLocalCoefficients m hm G 1 = identityCoefficients := by
  classical
  ext element
  change ((MonoidAlgebra.single 1 (1 : localCoefficientSubring m hm)).coeff element : ℂ) =
    if element = 1 then 1 else 0
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hequal : element = 1 <;> simp [hequal, Ne.symm]

theorem centralLocalCoefficients_mul (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G]
    (left right : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) :
    centralLocalCoefficients m hm G (left * right) =
      coefficientConvolution (centralLocalCoefficients m hm G left)
        (centralLocalCoefficients m hm G right) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  ext element
  simp only [centralLocalCoefficients, Subalgebra.coe_mul, coefficientConvolution_apply]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  · change (localCoefficientSubring m hm).subtype
      (∑ factor : G, left.val.coeff factor * right.val.coeff (factor⁻¹ * element)) = _
    rw [map_sum]
    simp only [map_mul, Subring.coe_subtype]
  · intro _
    exact zero_mul _

theorem centralLocalCoefficients_algebraMap (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] (scalar : localCoefficientSubring m hm) :
    centralLocalCoefficients m hm G
      (algebraMap (localCoefficientSubring m hm)
        (Subalgebra.center (localCoefficientSubring m hm)
          (MonoidAlgebra (localCoefficientSubring m hm) G)) scalar) =
      (scalar : ℂ) • identityCoefficients := by
  classical
  ext element
  simp only [centralLocalCoefficients, Subalgebra.coe_algebraMap]
  change ((MonoidAlgebra.single 1 scalar).coeff element : ℂ) =
    (scalar : ℂ) * (if element = 1 then 1 else 0)
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hequal : element = 1 <;> simp [hequal, Ne.symm]

@[expose] noncomputable def centralScalar (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (character : BlocksIrr G) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →+* localCoefficientSubring m hm where
  toFun value := ⟨BlocksCentralChar character.val (centralLocalCoefficients m hm G value),
    centralChar_localRing m hm character.property (centralLocalCoefficients_central m hm G value)⟩
  map_one' := by
    apply Subtype.ext
    change BlocksCentralChar character.val (centralLocalCoefficients m hm G 1) = 1
    rw [centralLocalCoefficients_one, centralChar_identityCoefficients character.property]
  map_mul' left right := by
    apply Subtype.ext
    change BlocksCentralChar character.val (centralLocalCoefficients m hm G (left * right)) =
      BlocksCentralChar character.val (centralLocalCoefficients m hm G left) *
        BlocksCentralChar character.val (centralLocalCoefficients m hm G right)
    rw [centralLocalCoefficients_mul, centralChar_convolution character.property _ _
      (centralLocalCoefficients_central m hm G left).2
      (centralLocalCoefficients_central m hm G right).2]
  map_zero' := by
    apply Subtype.ext
    change BlocksCentralChar character.val 0 = 0
    exact centralChar_zero _
  map_add' left right := by
    apply Subtype.ext
    change BlocksCentralChar character.val (centralLocalCoefficients m hm G (left + right)) =
      BlocksCentralChar character.val (centralLocalCoefficients m hm G left) +
        BlocksCentralChar character.val (centralLocalCoefficients m hm G right)
    rw [centralLocalCoefficients_add, centralChar_add]

@[expose] noncomputable def centralResidue (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (character : BlocksIrr G) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →+* localResidueField m hm :=
  (localResidue m hm).comp (centralScalar m hm G character)

@[expose] noncomputable def centralLocalElement (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Fintype G] (coefficients : G → ℂ)
    (hcoefficients : BlocksIsCentralR m coefficients) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) :=
  ⟨localCoefficientAlgebra m hm coefficients hcoefficients.1,
    groupAlgebra_mem_center_of_coeff_conj _ G (by
      intro element conjugator
      apply Subtype.ext
      simp only [localCoefficientAlgebra_coeff]
      exact hcoefficients.2 element conjugator)⟩

theorem centralLocalElement_coefficients (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Fintype G] (coefficients : G → ℂ)
    (hcoefficients : BlocksIsCentralR m coefficients) :
    centralLocalCoefficients m hm G (centralLocalElement m hm G coefficients hcoefficients) = coefficients := by
  ext element
  change ((localCoefficientAlgebra m hm coefficients hcoefficients.1).coeff element : ℂ) = _
  rw [localCoefficientAlgebra_coeff]

theorem centralScalar_algebraMap (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (character : BlocksIrr G)
    (scalar : localCoefficientSubring m hm) :
    centralScalar m hm G character
      (algebraMap (localCoefficientSubring m hm)
        (Subalgebra.center (localCoefficientSubring m hm)
          (MonoidAlgebra (localCoefficientSubring m hm) G)) scalar) = scalar := by
  apply Subtype.ext
  change BlocksCentralChar character.val (centralLocalCoefficients m hm G _) = (scalar : ℂ)
  rw [centralLocalCoefficients_algebraMap, centralChar_smul,
    centralChar_identityCoefficients character.property, mul_one]

@[expose] noncomputable def centralScalarAlgHom (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (character : BlocksIrr G) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →ₐ[localCoefficientSubring m hm]
        localCoefficientSubring m hm where
  __ := centralScalar m hm G character
  commutes' := centralScalar_algebraMap m hm G character

@[expose] noncomputable def centralResidueAlgHom (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (character : BlocksIrr G) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →ₐ[localCoefficientSubring m hm]
        localResidueField m hm :=
  (Algebra.ofId (localCoefficientSubring m hm) (localResidueField m hm)).comp
    (centralScalarAlgHom m hm G character)

noncomputable def centralScalarEmbedding (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →ₐ[localCoefficientSubring m hm]
        (BlocksIrr G → localCoefficientSubring m hm) where
  toFun value character := centralScalar m hm G character value
  map_one' := funext (fun character => map_one (centralScalar m hm G character))
  map_mul' left right := funext (fun character => map_mul (centralScalar m hm G character) left right)
  map_zero' := funext (fun character => map_zero (centralScalar m hm G character))
  map_add' left right := funext (fun character => map_add (centralScalar m hm G character) left right)
  commutes' scalar := funext (fun character => centralScalar_algebraMap m hm G character scalar)

theorem centralScalarEmbedding_injective (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] : Function.Injective (centralScalarEmbedding m hm G) := by
  intro left right hequal
  have hcoeff : centralLocalCoefficients m hm G left = centralLocalCoefficients m hm G right := by
    apply sub_eq_zero.mp
    apply centralChar_separates G
    · intro element conjugator
      simp only [Pi.sub_apply, (centralLocalCoefficients_central m hm G left).2 element conjugator,
        (centralLocalCoefficients_central m hm G right).2 element conjugator]
    · intro character hcharacter
      rw [centralChar_sub]
      apply sub_eq_zero.mpr
      exact congrArg Subtype.val (congrFun hequal ⟨character, hcharacter⟩)
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro element
  apply Subtype.ext
  exact congrFun hcoeff element

theorem centralSubalgebra_residue_extension (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G]
    (subalgebra : Subalgebra (localCoefficientSubring m hm)
      (Subalgebra.center (localCoefficientSubring m hm)
        (MonoidAlgebra (localCoefficientSubring m hm) G)))
    (residue : subalgebra →ₐ[localCoefficientSubring m hm] localResidueField m hm) :
    ∃ character : BlocksIrr G, ∀ value : subalgebra,
      residue value = centralResidue m hm G character value.val := by
  classical
  let : Finite (BlocksIrr G) := (irr_linearIndependent G).finite
  let : Fintype (BlocksIrr G) := Fintype.ofFinite _
  let embedding := centralScalarEmbedding m hm G
  let equivalence := subalgebra.equivMapOfInjective embedding (centralScalarEmbedding_injective m hm G)
  obtain ⟨character, hcharacter⟩ := finiteCoordinate_residue_extension (localCoefficientSubring m hm)
    (localResidueField m hm) (BlocksIrr G) (subalgebra.map embedding)
      (residue.comp equivalence.symm.toAlgHom)
  refine ⟨character, ?_⟩
  intro value
  have hequal := hcharacter (equivalence value)
  change residue (equivalence.symm (equivalence value)) = _ at hequal
  rw [equivalence.symm_apply_apply] at hequal
  exact hequal

theorem centralResidue_sameBlock (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (left right : BlocksIrr G)
    (hsame : right.val ∈ BlocksBlockOf m G left.val) :
    centralResidue m hm G left = centralResidue m hm G right := by
  apply RingHom.ext
  intro value
  apply (localResidue_eq_iff m hm _ _).mpr
  change BlocksCentralChar left.val (centralLocalCoefficients m hm G value) -
    BlocksCentralChar right.val (centralLocalCoefficients m hm G value) ∈ BlocksLocalMaxIdeal m
  have hcongr := sameBlock_centralChar_congr m hm G left.property hsame
    (centralLocalCoefficients_central m hm G value)
  convert localMaxIdeal_neg m hcongr using 1
  ring

end CFSG.BrauerThirdMainTheorem.Helpers
