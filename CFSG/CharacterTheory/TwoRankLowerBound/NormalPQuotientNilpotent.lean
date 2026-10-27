module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPGroupSimpleModule

public section

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

attribute [local instance] RestrictScalars.module

theorem field_ofModule_isIrreducible {field group vector : Type*}
    [Field field] [Group group] [AddCommGroup vector]
    [Module (MonoidAlgebra field group) vector]
    [IsSimpleModule (MonoidAlgebra field group) vector] :
    @Representation.IsIrreducible group field (RestrictScalars field (MonoidAlgebra field group) vector)
      _ _ _ (RestrictScalars.module field (MonoidAlgebra field group) vector)
      (Representation.ofModule (k := field) (G := group) vector) := by
  exact (Subrepresentation.submoduleSubrepresentationOrderIso
    (A := field) (G := group) (M := vector)).isSimpleOrder_iff.mp inferInstance

theorem representation_quotient_group_algebra_factor {field group vector : Type*}
    [Field field] [Group group] [AddCommGroup vector] [Module field vector]
    (representation : Representation field group vector)
    (subgroup : Subgroup group) [subgroup.Normal] (hkernel : subgroup ≤ representation.ker) :
    representation.asAlgebraHom =
      (show Representation field (group ⧸ subgroup) vector from
        QuotientGroup.lift subgroup representation hkernel).asAlgebraHom.comp
        (MonoidAlgebra.mapDomainAlgHom field field (QuotientGroup.mk' subgroup)) := by
  apply AlgHom.ext
  intro value
  induction value using MonoidAlgebra.induction_on with
  | of element =>
    change representation.asAlgebraHom (MonoidAlgebra.single element 1) =
      (show Representation field (group ⧸ subgroup) vector from
        QuotientGroup.lift subgroup representation hkernel).asAlgebraHom
        (MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup)
          (MonoidAlgebra.single element 1))
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one]
    exact (QuotientGroup.lift_mk subgroup hkernel element).symm
  | add left right hleft hright =>
    rw [map_add, map_add, hleft, hright]
  | smul scalar value hvalue =>
    rw [map_smul, map_smul, hvalue]

set_option backward.isDefEq.respectTransparency false in
theorem normal_p_quotient_kernel_le_jacobson {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) [subgroup.Normal] (hgroup : IsPGroup prime subgroup) :
    RingHom.ker (MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup)) ≤
      Ring.jacobson (MonoidAlgebra field group) := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  apply le_sInf
  intro ideal hmaximal
  let : IsSimpleModule (MonoidAlgebra field group) (MonoidAlgebra field group ⧸ ideal) :=
    isSimpleModule_iff_isCoatom.mpr (show ideal.IsMaximal from hmaximal).out
  let : Module field (RestrictScalars field (MonoidAlgebra field group)
      (MonoidAlgebra field group ⧸ ideal)) :=
    RestrictScalars.module field (MonoidAlgebra field group) (MonoidAlgebra field group ⧸ ideal)
  let representation := Representation.ofModule (k := field) (G := group)
    (MonoidAlgebra field group ⧸ ideal)
  let : representation.IsIrreducible := field_ofModule_isIrreducible
  have hkernel : subgroup ≤ representation.ker := by
    intro element hmember
    exact normal_p_subgroup_irreducible_action_trivial prime representation subgroup hgroup
      ⟨element, hmember⟩
  intro value hvalue
  have haction : representation.asAlgebraHom value = 0 := by
    rw [representation_quotient_group_algebra_factor representation subgroup hkernel,
      AlgHom.comp_apply]
    change (show Representation field (group ⧸ subgroup) _ from
      QuotientGroup.lift subgroup representation hkernel).asAlgebraHom
      (MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup) value) = 0
    rw [hvalue, map_zero]
  have hzero := congrArg (fun operator => operator
    ((RestrictScalars.addEquiv field (MonoidAlgebra field group)
      (MonoidAlgebra field group ⧸ ideal)).symm (Submodule.Quotient.mk (1 : MonoidAlgebra field group))))
    haction
  rw [Representation.ofModule_asAlgebraHom_apply_apply, LinearMap.zero_apply] at hzero
  have hquotient := congrArg
    (RestrictScalars.addEquiv field (MonoidAlgebra field group) (MonoidAlgebra field group ⧸ ideal)) hzero
  simp only [AddEquiv.apply_symm_apply, map_zero] at hquotient
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
    Submodule.Quotient.mk_eq_zero] at hquotient
  exact hquotient

theorem normal_p_quotient_kernel_nilpotent {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) [subgroup.Normal] (hgroup : IsPGroup prime subgroup) :
    IsNilpotent (RingHom.ker (MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup))) := by
  let : IsArtinianRing (MonoidAlgebra field group) := IsArtinianRing.of_finite field _
  obtain ⟨exponent, hpower⟩ := IsSemiprimaryRing.isNilpotent (R := MonoidAlgebra field group)
  refine ⟨exponent, ?_⟩
  apply le_antisymm _ bot_le
  exact (ideal_pow_mono _ _
    (normal_p_quotient_kernel_le_jacobson (field := field) prime subgroup hgroup) exponent).trans
    (by simpa only [hpower, Ideal.zero_eq_bot] using (le_refl (⊥ : Ideal (MonoidAlgebra field group))))

theorem normal_p_quotient_zero_element_nilpotent {field group : Type*}
    [Field field] [Group group] [Finite group] (prime : ℕ) [Fact prime.Prime] [CharP field prime]
    (subgroup : Subgroup group) [subgroup.Normal] (hgroup : IsPGroup prime subgroup)
    (value : MonoidAlgebra field group)
    (hzero : MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup) value = 0) :
    IsNilpotent value := by
  obtain ⟨exponent, hpower⟩ := normal_p_quotient_kernel_nilpotent (field := field) prime subgroup hgroup
  refine ⟨exponent, ?_⟩
  have hmember := Ideal.pow_mem_pow
    (I := RingHom.ker (MonoidAlgebra.mapDomainRingHom field (QuotientGroup.mk' subgroup))) hzero exponent
  rw [hpower, Ideal.zero_eq_bot, Ideal.mem_bot] at hmember
  exact hmember

end CFSG.TwoRankLowerBound.Helpers
