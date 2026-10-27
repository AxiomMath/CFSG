module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CharacterTransport
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def commonCentralAlgebra (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] (inclusion : small →* large) :
    Subalgebra (localCoefficientSubring m hm)
      (Subalgebra.center (localCoefficientSubring m hm)
        (MonoidAlgebra (localCoefficientSubring m hm) small)) :=
  (Subalgebra.center (localCoefficientSubring m hm)
    (MonoidAlgebra (localCoefficientSubring m hm) large)).comap
      ((MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm) (localCoefficientSubring m hm) inclusion).comp
        (Subalgebra.center (localCoefficientSubring m hm)
          (MonoidAlgebra (localCoefficientSubring m hm) small)).val)

@[expose] noncomputable def commonCentralInclusion (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] (inclusion : small →* large) :
    commonCentralAlgebra m hm small large inclusion →ₐ[localCoefficientSubring m hm]
      (Subalgebra.center (localCoefficientSubring m hm)
        (MonoidAlgebra (localCoefficientSubring m hm) large)) :=
  (((MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm) (localCoefficientSubring m hm) inclusion).comp
    (Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) small)).val).comp
        (commonCentralAlgebra m hm small large inclusion).val).codRestrict _ (fun value => value.property)

theorem commonCentralInclusion_injective (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] (inclusion : small →* large)
    (hinjective : Function.Injective inclusion) :
    Function.Injective (commonCentralInclusion m hm small large inclusion) := by
  intro left right hequal
  apply Subtype.ext
  apply Subtype.ext
  apply MonoidAlgebra.mapDomain_injective hinjective
  exact congrArg Subtype.val hequal

theorem commonCentralInclusion_augmentation (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] [Finite small] [Finite large]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (value : commonCentralAlgebra m hm small large inclusion) :
    BlocksCentralChar (fun _ => 1)
      (centralLocalCoefficients m hm large (commonCentralInclusion m hm small large inclusion value)) =
      BlocksCentralChar (fun _ => 1) (centralLocalCoefficients m hm small value.val) := by
  classical
  let : Fintype small := Fintype.ofFinite _
  let : Fintype large := Fintype.ofFinite _
  rw [centralChar_trivial, centralChar_trivial, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  change (∑ element : large, ((MonoidAlgebra.mapDomain inclusion value.val.val).coeff element : ℂ)) =
    ∑ element : small, (value.val.val.coeff element : ℂ)
  rw [MonoidAlgebra.coeff_mapDomain]
  rw [← Finsupp.sum_fintype (Finsupp.mapDomain inclusion value.val.val.coeff)
    (fun _ coefficient => (coefficient : ℂ)) (fun _ => rfl),
    Finsupp.sum_mapDomain_index_inj hinjective,
    Finsupp.sum_fintype value.val.val.coeff (fun _ coefficient => (coefficient : ℂ)) (fun _ => rfl)]

theorem commonCentral_mono (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small middle large : Type*) [Group small] [Group middle] [Group large]
    (first : small →* middle) (second : middle →* large)
    (hinjective : Function.Injective second) :
    commonCentralAlgebra m hm small large (second.comp first) ≤
      commonCentralAlgebra m hm small middle first := by
  intro value hvalue
  apply (Subalgebra.mem_center_iff (R := localCoefficientSubring m hm)).mpr
  intro coefficient
  apply MonoidAlgebra.mapDomain_injective hinjective
  let firstMap := MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm)
    (localCoefficientSubring m hm) first
  let secondMap := MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm)
    (localCoefficientSubring m hm) second
  change secondMap (coefficient * firstMap value.val) = secondMap (firstMap value.val * coefficient)
  rw [map_mul, map_mul]
  have hcenter := (Subalgebra.mem_center_iff (R := localCoefficientSubring m hm)).mp hvalue
    (secondMap coefficient)
  change secondMap coefficient *
    (MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm) (localCoefficientSubring m hm)
      (second.comp first)) value.val =
    (MonoidAlgebra.mapDomainAlgHom (localCoefficientSubring m hm) (localCoefficientSubring m hm)
      (second.comp first)) value.val * secondMap coefficient at hcenter
  rw [MonoidAlgebra.mapDomainAlgHom_comp] at hcenter
  exact hcenter

theorem commonCentralRestriction_coefficients (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] [Fintype small]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (coefficients : large → ℂ) (hcoefficients : BlocksIsCentralR m coefficients) (element : large) :
    ((MonoidAlgebra.mapDomain inclusion
      (localCoefficientAlgebra m hm (coefficients ∘ inclusion)
        (fun factor => hcoefficients.1 (inclusion factor)))).coeff element : ℂ) =
      (Set.range inclusion).indicator coefficients element := by
  classical
  rw [MonoidAlgebra.coeff_mapDomain]
  by_cases hmember : element ∈ Set.range inclusion
  · obtain ⟨factor, rfl⟩ := hmember
    rw [Finsupp.mapDomain_apply_of_injective hinjective, localCoefficientAlgebra_coeff]
    have hmem : inclusion factor ∈ Set.range inclusion := ⟨factor, rfl⟩
    exact (Set.indicator_of_mem hmem coefficients).symm
  · rw [Finsupp.mapDomain_of_notMem_range _ _ hmember]
    exact (Set.indicator_of_notMem hmember coefficients).symm

theorem commonCentralRestriction_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] [Fintype small]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (coefficients : large → ℂ) (hcoefficients : BlocksIsCentralR m coefficients)
    (hprojected : BlocksIsCentralR m ((Set.range inclusion).indicator coefficients)) :
    centralLocalElement m hm small (coefficients ∘ inclusion)
      ⟨fun factor => hcoefficients.1 (inclusion factor), by
        intro element conjugator
        simp only [Function.comp_apply, map_mul, map_inv, hcoefficients.2]⟩ ∈
      commonCentralAlgebra m hm small large inclusion := by
  apply groupAlgebra_mem_center_of_coeff_conj _ large
  intro element conjugator
  apply Subtype.ext
  change ((MonoidAlgebra.mapDomain inclusion
    (localCoefficientAlgebra m hm (coefficients ∘ inclusion)
      (fun factor => hcoefficients.1 (inclusion factor)))).coeff
        (conjugator * element * conjugator⁻¹) : ℂ) =
      ((MonoidAlgebra.mapDomain inclusion
        (localCoefficientAlgebra m hm (coefficients ∘ inclusion)
          (fun factor => hcoefficients.1 (inclusion factor)))).coeff element : ℂ)
  rw [commonCentralRestriction_coefficients m hm small large inclusion hinjective coefficients hcoefficients,
    commonCentralRestriction_coefficients m hm small large inclusion hinjective coefficients hcoefficients]
  exact hprojected.2 element conjugator

@[expose] noncomputable def commonCentralRestriction (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] [Fintype small]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (coefficients : large → ℂ) (hcoefficients : BlocksIsCentralR m coefficients)
    (hprojected : BlocksIsCentralR m ((Set.range inclusion).indicator coefficients)) :
    commonCentralAlgebra m hm small large inclusion :=
  ⟨centralLocalElement m hm small (coefficients ∘ inclusion)
    ⟨fun factor => hcoefficients.1 (inclusion factor), by
      intro element conjugator
      simp only [Function.comp_apply, map_mul, map_inv, hcoefficients.2]⟩,
    commonCentralRestriction_mem m hm small large inclusion hinjective coefficients hcoefficients hprojected⟩

theorem commonCentralRestriction_inclusion (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type*) [Group small] [Group large] [Fintype small]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (coefficients : large → ℂ) (hcoefficients : BlocksIsCentralR m coefficients)
    (hprojected : BlocksIsCentralR m ((Set.range inclusion).indicator coefficients)) :
    centralLocalCoefficients m hm large (commonCentralInclusion m hm small large inclusion
      (commonCentralRestriction m hm small large inclusion hinjective coefficients hcoefficients hprojected)) =
        (Set.range inclusion).indicator coefficients := by
  ext element
  exact commonCentralRestriction_coefficients m hm small large inclusion hinjective coefficients hcoefficients element

theorem commonCentral_residue_extension (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type) [Group small] [Group large] [Finite small] [Finite large]
    (inclusion : small →* large) (character : BlocksIrr large) :
    ∃ smallCharacter : BlocksIrr small, ∀ value : commonCentralAlgebra m hm small large inclusion,
      centralResidue m hm large character (commonCentralInclusion m hm small large inclusion value) =
        centralResidue m hm small smallCharacter value.val := by
  exact centralSubalgebra_residue_extension m hm small _
    ((centralResidueAlgHom m hm large character).comp (commonCentralInclusion m hm small large inclusion))

theorem principalLocalElement_invariant (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type) [Group small] [Group large] [Fintype small]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (hconjugation : ∀ conjugator : large, ∃ equivalence : small ≃* small,
      ∀ element : small, inclusion (equivalence element) = conjugator * inclusion element * conjugator⁻¹) :
    centralLocalElement m hm small (BlocksIdempotentCoeff small (BlocksPrincipalBlock m small))
      (idempotentCoeff_central m small (block_admissible m hm small (principal_isBlock m small))) ∈
        commonCentralAlgebra m hm small large inclusion := by
  classical
  apply groupAlgebra_mem_center_of_coeff_conj _ large
  intro element conjugator
  obtain ⟨equivalence, hequivalence⟩ := hconjugation conjugator
  let value := localCoefficientAlgebra m hm
    (BlocksIdempotentCoeff small (BlocksPrincipalBlock m small))
    (block_admissible m hm small (principal_isBlock m small)).2
  change (MonoidAlgebra.mapDomain inclusion value).coeff (conjugator * element * conjugator⁻¹) =
    (MonoidAlgebra.mapDomain inclusion value).coeff element
  rw [MonoidAlgebra.coeff_mapDomain]
  by_cases hmember : element ∈ Set.range inclusion
  · obtain ⟨factor, rfl⟩ := hmember
    rw [← hequivalence, Finsupp.mapDomain_apply_of_injective hinjective, Finsupp.mapDomain_apply_of_injective hinjective]
    apply Subtype.ext
    simp only [value, localCoefficientAlgebra_coeff]
    exact congrFun (principalIdempotent_comp_equiv m hm equivalence) factor
  · have hconj : conjugator * element * conjugator⁻¹ ∉ Set.range inclusion := by
      rintro ⟨factor, hfactor⟩
      apply hmember
      refine ⟨equivalence.symm factor, ?_⟩
      have hequal := hequivalence (equivalence.symm factor)
      rw [equivalence.apply_symm_apply, hfactor] at hequal
      have hcancel : Function.Injective (fun factor : large => conjugator * factor * conjugator⁻¹) := by
        intro left right hequal
        exact mul_left_cancel (mul_right_cancel hequal)
      exact hcancel hequal.symm
    rw [Finsupp.mapDomain_of_notMem_range value.coeff _ hconj,
      Finsupp.mapDomain_of_notMem_range value.coeff _ hmember]

theorem commonCentral_reverse_residue_extension (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (small large : Type) [Group small] [Group large] [Finite small] [Finite large]
    (inclusion : small →* large) (hinjective : Function.Injective inclusion)
    (smallCharacter : BlocksIrr small) :
    ∃ character : BlocksIrr large, ∀ value : commonCentralAlgebra m hm small large inclusion,
      centralResidue m hm large character (commonCentralInclusion m hm small large inclusion value) =
        centralResidue m hm small smallCharacter value.val := by
  let embedding := commonCentralInclusion m hm small large inclusion
  let equivalence := (⊤ : Subalgebra (localCoefficientSubring m hm)
    (commonCentralAlgebra m hm small large inclusion)).equivMapOfInjective embedding
      (commonCentralInclusion_injective m hm small large inclusion hinjective)
  let residue := (centralResidueAlgHom m hm small smallCharacter).comp
    (commonCentralAlgebra m hm small large inclusion).val
  obtain ⟨character, hcharacter⟩ := centralSubalgebra_residue_extension m hm large
    ((⊤ : Subalgebra (localCoefficientSubring m hm)
      (commonCentralAlgebra m hm small large inclusion)).map embedding)
        ((residue.comp (⊤ : Subalgebra (localCoefficientSubring m hm)
          (commonCentralAlgebra m hm small large inclusion)).val).comp equivalence.symm.toAlgHom)
  refine ⟨character, ?_⟩
  intro value
  have hequal := hcharacter (equivalence ⟨value, trivial⟩)
  change residue (equivalence.symm (equivalence ⟨value, trivial⟩)).val = _ at hequal
  rw [equivalence.symm_apply_apply] at hequal
  exact hequal.symm

end CFSG.BrauerThirdMainTheorem.Helpers
