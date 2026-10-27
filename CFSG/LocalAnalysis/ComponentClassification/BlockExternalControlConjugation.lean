module

public import CFSG.LocalAnalysis.ComponentClassification.BlockFactorContainment
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation

public section

namespace CFSG.ComponentClassification.BlockExternalControlConjugation

theorem normalizer_mem {G : Type*} [Group G] (component : Subgroup G) (actor member : G) :
    (MulAut.conj actor) member ∈ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor) ↔
      member ∈ UniversalOrbitBlock.normalizer component := by
  rw [← OrbitBlockConjugation.normalizer component actor]
  exact Subgroup.mem_map_iff_mem (MulAut.conj actor).injective

theorem fusion {G : Type*} [Group G] (component : Subgroup G) (actor member : G)
    (hmember : member ∈ BlockFusion.involutions component) :
    (MulAut.conj actor) member ∈ BlockFusion.involutions (UniversalOrbitBlock.conjugate component actor) := by
  obtain ⟨horder, factor, hfactor, hcentralizes⟩ := hmember
  refine ⟨(orderOf_injective (MulAut.conj actor).toMonoidHom (MulAut.conj actor).injective member).trans horder,
    UniversalOrbitBlock.conjugate factor actor, (OrbitBlockConjugation.block component factor actor).mpr hfactor, ?_⟩
  have hmap := Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom hcentralizes
  rw [UniversalComponentBlock.subgroup_centralizer_map] at hmap
  exact hmap

theorem control {G : Type*} [Group G] (component : Subgroup G) (actor : G)
    (hcontrol : BlockFactorContainment.ExternalControl component) :
    BlockFactorContainment.ExternalControl (UniversalOrbitBlock.conjugate component actor) := by
  let equivalence := MulAut.conj actor
  intro member hmember transporter houtside himage factor hfactor
  let preMember := equivalence.symm member
  let preTransporter := equivalence.symm transporter
  let preFactor := UniversalOrbitBlock.conjugate factor actor⁻¹
  have hpreFusion : preMember ∈ BlockFusion.involutions component := by
    have hmem := fusion (UniversalOrbitBlock.conjugate component actor) actor⁻¹ member hmember
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
    change actor⁻¹ * member * actor⁻¹⁻¹ ∈ BlockFusion.involutions component at hmem
    rw [inv_inv] at hmem
    exact hmem
  have hpreOutside : preTransporter ∉ UniversalOrbitBlock.normalizer component := by
    intro hmem
    have himage := (normalizer_mem component actor preTransporter).mpr hmem
    rw [MulEquiv.apply_symm_apply] at himage
    exact houtside himage
  have hpreImage : (MulAut.conj preTransporter) preMember ∈ UniversalOrbitBlock.normalizer component := by
    apply (normalizer_mem component actor _).mp
    have heq : equivalence ((MulAut.conj preTransporter) preMember) = (MulAut.conj transporter) member := by
      simp only [MulAut.conj_apply, map_mul, map_inv]
      rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    change equivalence ((MulAut.conj preTransporter) preMember) ∈
      UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)
    rw [heq]
    exact himage
  have hpreFactor : preFactor ∈ UniversalOrbitBlock.block component := by
    have hmem := (OrbitBlockConjugation.block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
    rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
  have hfixed := hcontrol preMember hpreFusion preTransporter hpreOutside hpreImage preFactor hpreFactor
  have hmap := congrArg (fun candidate : Subgroup G => UniversalOrbitBlock.conjugate candidate actor) hfixed
  have hpreFactorMap : UniversalOrbitBlock.conjugate preFactor actor = factor := by
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate factor actor⁻¹) actor = factor
    rw [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one]
  have hconjEquivariant : ∀ candidate : Subgroup G, ∀ element : G,
      UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate candidate element) actor =
        UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate candidate actor) (equivalence element) := by
    intro candidate element
    rw [UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate]
    congr 1
    change actor * element = (actor * element * actor⁻¹) * actor
    group
  rw [hconjEquivariant, hpreFactorMap] at hmap
  have helementEq : equivalence ((MulAut.conj preTransporter) preMember) = (MulAut.conj transporter) member := by
    simp only [MulAut.conj_apply, map_mul, map_inv]
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rwa [helementEq] at hmap

end CFSG.ComponentClassification.BlockExternalControlConjugation
