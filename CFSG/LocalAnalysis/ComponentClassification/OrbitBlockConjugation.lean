module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ComponentClassification.OrbitBlockConjugation

theorem orbit {G : Type*} [Group G] (component factor : Subgroup G) (actor : G) :
    UniversalOrbitBlock.conjugate factor actor ∈
      UniversalOrbitBlock.orbit (UniversalOrbitBlock.conjugate component actor) ↔
        factor ∈ UniversalOrbitBlock.orbit component := by
  constructor
  · rintro ⟨preimage, heq⟩
    have hmap := congrArg (fun subgroup : Subgroup G => UniversalOrbitBlock.conjugate subgroup actor⁻¹) heq
    rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one,
      UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate] at hmap
    exact ⟨actor⁻¹ * preimage * actor, hmap⟩
  · rintro ⟨preimage, heq⟩
    refine ⟨actor * preimage * actor⁻¹, ?_⟩
    rw [heq, UniversalOrbitBlock.conjugate_conjugate, UniversalOrbitBlock.conjugate_conjugate]
    congr 1
    group

theorem block {G : Type*} [Group G] (component factor : Subgroup G) (actor : G) :
    UniversalOrbitBlock.conjugate factor actor ∈
      UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor) ↔
        factor ∈ UniversalOrbitBlock.block component := by
  exact and_congr (orbit component factor actor)
    (UniversalComponentBlock.related_map_iff (MulAut.conj actor) factor component)

@[expose] noncomputable def equivalence {G : Type*} [Group G] (component : Subgroup G) (actor : G) :
    UniversalOrbitBlock.block component ≃ UniversalOrbitBlock.block (UniversalOrbitBlock.conjugate component actor) :=
  { toFun := fun factor => ⟨UniversalOrbitBlock.conjugate factor.val actor, (block component factor.val actor).mpr factor.property⟩
    invFun := fun factor => ⟨UniversalOrbitBlock.conjugate factor.val actor⁻¹, by
      have hmem := (block (UniversalOrbitBlock.conjugate component actor) factor.val actor⁻¹).mpr factor.property
      rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem⟩
    left_inv := by
      intro factor
      apply Subtype.ext
      exact (UniversalOrbitBlock.conjugate_conjugate factor.val actor actor⁻¹).trans
        (by rw [inv_mul_cancel, UniversalOrbitBlock.conjugate_one])
    right_inv := by
      intro factor
      apply Subtype.ext
      exact (UniversalOrbitBlock.conjugate_conjugate factor.val actor⁻¹ actor).trans
        (by rw [mul_inv_cancel, UniversalOrbitBlock.conjugate_one]) }

theorem generated {G : Type*} [Group G] (component : Subgroup G) (actor : G) :
    (UniversalOrbitBlock.generated component).map (MulAut.conj actor).toMonoidHom =
      UniversalOrbitBlock.generated (UniversalOrbitBlock.conjugate component actor) := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro factor hfactor
    apply Subgroup.map_le_iff_le_comap.mp
    exact CommutingComponentFamily.factor_le _ _ ((block component factor actor).mpr hfactor)
  · apply sSup_le
    intro factor hfactor
    let original := UniversalOrbitBlock.conjugate factor actor⁻¹
    have horiginal : original ∈ UniversalOrbitBlock.block component := by
      have hmem := (block (UniversalOrbitBlock.conjugate component actor) factor actor⁻¹).mpr hfactor
      rwa [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one] at hmem
    have hmap := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (CommutingComponentFamily.factor_le _ original horiginal)
    change UniversalOrbitBlock.conjugate original actor ≤ _ at hmap
    change UniversalOrbitBlock.conjugate (UniversalOrbitBlock.conjugate factor actor⁻¹) actor ≤ _ at hmap
    rwa [UniversalOrbitBlock.conjugate_conjugate, mul_inv_cancel, UniversalOrbitBlock.conjugate_one] at hmap

theorem normalizer {G : Type*} [Group G] (component : Subgroup G) (actor : G) :
    (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom =
      UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor) := by
  change (Subgroup.normalizer (UniversalOrbitBlock.generated component : Set G)).map (MulAut.conj actor).toMonoidHom = _
  rw [Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj actor).bijective, generated]
  rfl

theorem inverse_outside {G : Type*} [Group G] (component : Subgroup G) (actor : G)
    (hactor : actor ∉ UniversalOrbitBlock.normalizer component) :
    actor⁻¹ ∉ UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor) := by
  intro hmem
  rw [← normalizer] at hmem
  obtain ⟨original, horiginal, heq⟩ := Subgroup.mem_map.mp hmem
  have hidentity : original = actor⁻¹ := by
    have hmap := congrArg (fun member : G => actor⁻¹ * member * actor) heq
    change actor⁻¹ * (actor * original * actor⁻¹) * actor = actor⁻¹ * actor⁻¹ * actor at hmap
    convert hmap using 1 <;> group
  rw [hidentity] at horiginal
  exact hactor ((UniversalOrbitBlock.normalizer component).inv_mem_iff.mp horiginal)

theorem normalizer_back {G : Type*} [Group G] (component : Subgroup G) (actor : G) :
    (UniversalOrbitBlock.normalizer (UniversalOrbitBlock.conjugate component actor)).map
      (MulAut.conj actor⁻¹).toMonoidHom = UniversalOrbitBlock.normalizer component := by
  rw [normalizer]
  rw [UniversalOrbitBlock.conjugate_conjugate, inv_mul_cancel, UniversalOrbitBlock.conjugate_one]

end CFSG.ComponentClassification.OrbitBlockConjugation
