module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ProjectionMultiplicativity

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

@[expose] noncomputable def centerReduction (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →ₐ[localCoefficientSubring m hm]
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localResidueField m hm) G) :=
  ((MonoidAlgebra.mapAlgHom G
      (Algebra.ofId (localCoefficientSubring m hm) (localResidueField m hm))).comp
      (Subalgebra.center _ _).val).codRestrict (Subalgebra.center _ _) (by
    intro value
    apply groupAlgebra_mem_center_of_coeff_conj
    intro element conjugator
    change localResidue m hm (value.val.coeff (conjugator * element * conjugator⁻¹)) =
      localResidue m hm (value.val.coeff element)
    rw [groupAlgebra_center_coeff_conj _ G value.property])

theorem centerReduction_coeff (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G]
    (value : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) (element : G) :
    (centerReduction m hm G value).val.coeff element =
      localResidue m hm (value.val.coeff element) := rfl

@[expose] noncomputable def localBrauerElement (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    (value : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) overgroup) := by
  classical
  let : Fintype overgroup := Fintype.ofFinite _
  exact centralLocalElement m hm overgroup
    (BlocksBrauerProj subgroup overgroup (centralLocalCoefficients m hm G value))
    (brauerProj_central m hm subgroup overgroup hnormalizer
      (centralLocalCoefficients_central m hm G value))

theorem localBrauerElement_coefficients (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G))
    (value : Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G)) :
    centralLocalCoefficients m hm overgroup
      (localBrauerElement m hm G subgroup overgroup hnormalizer value) =
      BlocksBrauerProj subgroup overgroup (centralLocalCoefficients m hm G value) := by
  classical
  let : Fintype overgroup := Fintype.ofFinite _
  exact centralLocalElement_coefficients m hm overgroup _
    (brauerProj_central m hm subgroup overgroup hnormalizer
      (centralLocalCoefficients_central m hm G value))

theorem centralLocalCoefficients_injective (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type*) [Group G] : Function.Injective (centralLocalCoefficients m hm G) := by
  intro left right hequal
  apply Subtype.ext
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro element
  apply Subtype.ext
  exact congrFun hequal element

theorem brauerProj_add {G : Type*} [Group G] (subgroup overgroup : Subgroup G)
    (left right : G → ℂ) :
    BlocksBrauerProj subgroup overgroup (left + right) =
      BlocksBrauerProj subgroup overgroup left + BlocksBrauerProj subgroup overgroup right := by
  ext element
  simp only [Pi.add_apply]
  rw [brauerProj_apply, brauerProj_apply, brauerProj_apply]
  split_ifs <;> simp only [Pi.add_apply, add_zero]

theorem brauerProj_identity {G : Type*} [Group G] (subgroup overgroup : Subgroup G) :
    BlocksBrauerProj subgroup overgroup (identityCoefficients : G → ℂ) = identityCoefficients := by
  classical
  ext element
  rw [brauerProj_apply]
  by_cases hequal : element = 1
  · subst element
    simp only [Subgroup.coe_one, (Subgroup.centralizer _).one_mem,
      identityCoefficients, ↓reduceIte]
  · have hval : element.val ≠ 1 := fun hval => hequal (Subtype.ext hval)
    simp only [identityCoefficients, ite_eq_right hequal, ite_eq_right hval, ite_self]

@[expose] noncomputable def reducedBrauerProjection
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (prime : ℕ) (hprime : prime.Prime)
    (hprimeMem : (prime : BlocksAlgInt) ∈ m) (G : Type*) [Group G] [Finite G]
    (subgroup overgroup : Subgroup G) (hpGroup : IsPGroup prime subgroup)
    (hcentralizer : Subgroup.centralizer (subgroup : Set G) ≤ overgroup)
    (hnormalizer : overgroup ≤ Subgroup.normalizer (subgroup : Set G)) :
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localCoefficientSubring m hm) G) →ₐ[localCoefficientSubring m hm]
    Subalgebra.center (localCoefficientSubring m hm)
      (MonoidAlgebra (localResidueField m hm) overgroup) where
  toFun value := centerReduction m hm overgroup
    (localBrauerElement m hm G subgroup overgroup hnormalizer value)
  map_one' := by
    have hone : localBrauerElement m hm G subgroup overgroup hnormalizer 1 = 1 := by
      apply centralLocalCoefficients_injective m hm overgroup
      rw [localBrauerElement_coefficients, centralLocalCoefficients_one,
        centralLocalCoefficients_one, brauerProj_identity]
    rw [hone, map_one]
  map_mul' left right := by
    apply Subtype.ext
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro element
    rw [← map_mul]
    simp only [centerReduction_coeff]
    apply (localResidue_eq_iff m hm _ _).mpr
    change centralLocalCoefficients m hm overgroup
      (localBrauerElement m hm G subgroup overgroup hnormalizer (left * right)) element -
      centralLocalCoefficients m hm overgroup
        (localBrauerElement m hm G subgroup overgroup hnormalizer left *
          localBrauerElement m hm G subgroup overgroup hnormalizer right) element ∈
        BlocksLocalMaxIdeal m
    rw [localBrauerElement_coefficients, centralLocalCoefficients_mul,
      centralLocalCoefficients_mul, localBrauerElement_coefficients, localBrauerElement_coefficients]
    exact brauerProj_convolution_congr m hm prime hprime hprimeMem subgroup overgroup
      hpGroup hcentralizer (centralLocalCoefficients_central m hm G left)
      (centralLocalCoefficients_central m hm G right) element
  map_zero' := by
    classical
    have hzero : localBrauerElement m hm G subgroup overgroup hnormalizer 0 = 0 := by
      apply centralLocalCoefficients_injective m hm overgroup
      rw [localBrauerElement_coefficients]
      ext element
      rw [brauerProj_apply]
      change (if _ then (0 : ℂ) else 0) = 0
      exact ite_self 0
    rw [hzero, map_zero]
  map_add' left right := by
    have hadd : localBrauerElement m hm G subgroup overgroup hnormalizer (left + right) =
        localBrauerElement m hm G subgroup overgroup hnormalizer left +
          localBrauerElement m hm G subgroup overgroup hnormalizer right := by
      apply centralLocalCoefficients_injective m hm overgroup
      rw [localBrauerElement_coefficients, centralLocalCoefficients_add,
        centralLocalCoefficients_add, localBrauerElement_coefficients,
        localBrauerElement_coefficients, brauerProj_add]
    rw [hadd, map_add]
  commutes' scalar := by
    have hscalar : localBrauerElement m hm G subgroup overgroup hnormalizer
        (algebraMap (localCoefficientSubring m hm) _ scalar) =
        algebraMap (localCoefficientSubring m hm) _ scalar := by
      apply centralLocalCoefficients_injective m hm overgroup
      rw [localBrauerElement_coefficients, centralLocalCoefficients_algebraMap,
        centralLocalCoefficients_algebraMap]
      ext element
      rw [brauerProj_apply]
      by_cases hequal : element = 1
      · subst element
        simp only [Subgroup.coe_one, (Subgroup.centralizer _).one_mem,
          Pi.smul_apply, smul_eq_mul, identityCoefficients, ↓reduceIte]
      · have hval : element.val ≠ 1 := fun hval => hequal (Subtype.ext hval)
        simp only [Pi.smul_apply, smul_eq_mul, identityCoefficients, ite_eq_right hequal,
          ite_eq_right hval, mul_zero, ite_self]
    rw [hscalar, AlgHom.commutes]

end CFSG.BrauerThirdMainTheorem.Helpers
