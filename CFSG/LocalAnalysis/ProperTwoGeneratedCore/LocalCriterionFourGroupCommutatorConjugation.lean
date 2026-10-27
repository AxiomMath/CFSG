module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorCoefficient

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

@[expose, instance_reducible] def normalizedSubgroupAction (J V : Subgroup G) (hV : V ≤ Subgroup.normalizer (J : Set G)) :
    MulDistribMulAction V J :=
  MulDistribMulAction.compHom J (J.normalizerMonoidHom.comp (Subgroup.inclusion hV))

theorem normalizedSubgroupAction_smul_coe (J V : Subgroup G) (hV : V ≤ Subgroup.normalizer (J : Set G))
    (c : V) (x : J) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    ((c • x : J) : G) = (c : G) * (x : G) * (c : G)⁻¹ := rfl

theorem normalized_fixed_map (J V : Subgroup G) (hV : V ≤ Subgroup.normalizer (J : Set G)) (c : V) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    (actorFixedSubgroup (I := J) c).map J.subtype =
      J ⊓ Subgroup.centralizer {(c : G)} := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    change y ∈ actorFixedSubgroup (I := J) c at hy
    have hf : c • y = y := (mem_actorFixedSubgroup c y).mp hy
    have h : (c : G) * (y : G) * (c : G)⁻¹ = (y : G) :=
      congrArg Subtype.val hf
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · rintro ⟨hxJ, hxC⟩
    refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
    change (⟨x, hxJ⟩ : J) ∈ actorFixedSubgroup (I := J) c
    apply (mem_actorFixedSubgroup c _).mpr
    apply Subtype.ext
    change (c : G) * x * (c : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm

theorem normalized_commutator_map (J V : Subgroup G) (hV : V ≤ Subgroup.normalizer (J : Set G))
    (c : V) (hc : (c : G) * (c : G) = 1) (Q : Subgroup J) :
    let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
    (actorCommutatorSubgroup c Q).map J.subtype =
      ⁅Q.map J.subtype, Subgroup.zpowers (c : G)⁆ := by
  let : MulDistribMulAction V J := normalizedSubgroupAction J V hV
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (actorCommutatorSubgroup_le c Q _).mpr
    intro x hx
    change (x : G)⁻¹ * ((c : G) * (x : G) * (c : G)⁻¹) ∈
      ⁅Q.map J.subtype, Subgroup.zpowers (c : G)⁆
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_map_of_mem J.subtype (Q.inv_mem hx))
      (Subgroup.mem_zpowers (c : G))
    simpa only [commutatorElement_def, map_inv, inv_inv, Subgroup.subtype_apply, mul_assoc] using h
  · apply Subgroup.commutator_le.mpr
    intro x hx y hy
    obtain ⟨q, hq, rfl⟩ := hx
    rcases (mem_zpowers_of_square_one hc).mp hy with rfl | rfl
    · simpa only [commutatorElement_one_right] using
        ((actorCommutatorSubgroup c Q).map J.subtype).one_mem
    · have h := Subgroup.mem_map_of_mem J.subtype
        (actorCommutatorSubgroup_generator_mem c (Q.inv_mem hq))
      simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv,
        normalizedSubgroupAction_smul_coe] at h
      simpa only [commutatorElement_def, Subgroup.subtype_apply, mul_assoc] using h

end CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
