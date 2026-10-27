module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def perfectResidual (G : Type*) [Group G] : Subgroup G := ⨅ index, derivedSeries G index

theorem finite_perfectResidual_eq_derivedSeries
    {G : Type*} [Group G] [Finite G] :
    ∃ index, perfectResidual G = derivedSeries G index := by
  classical
  obtain ⟨minimalGroup, hminimal⟩ := (Set.toFinite (Set.range (derivedSeries G))).exists_minimal
    ⟨derivedSeries G 0, ⟨0, rfl⟩⟩
  obtain ⟨index, rfl⟩ := hminimal.prop
  refine ⟨index, le_antisymm (iInf_le _ index) ?_⟩
  apply le_iInf
  intro otherIndex
  have hcommon : derivedSeries G (max index otherIndex) = derivedSeries G index :=
    hminimal.eq_of_le ⟨max index otherIndex, rfl⟩
      (derivedSeries_antitone G (le_max_left _ _))
  rw [← hcommon]
  exact derivedSeries_antitone G (le_max_right _ _)

theorem perfectResidual_characteristic
    {G : Type*} [Group G] : (perfectResidual G).Characteristic := by
  unfold perfectResidual
  infer_instance

theorem finite_perfectResidual_isPerfect
    {G : Type*} [Group G] [Finite G] : Group.IsPerfect (perfectResidual G) := by
  obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
  have hnext : derivedSeries G (index + 1) = derivedSeries G index := by
    apply le_antisymm (derivedSeries_antitone G (Nat.le_succ index))
    rw [← hindex]
    exact iInf_le _ (index + 1)
  apply Subgroup.isPerfect_iff.mpr
  rw [hindex]
  rwa [derivedSeries_succ] at hnext

theorem finite_perfectResidual_surjects_to_perfect_image
    {G Image : Type*} [Group G] [Finite G] [Group Image] [Group.IsPerfect Image]
    (homomorphism : G →* Image) (hsurjective : Function.Surjective homomorphism) :
    Subgroup.map homomorphism (perfectResidual G) = ⊤ := by
  obtain ⟨index, hindex⟩ := finite_perfectResidual_eq_derivedSeries (G := G)
  have himage := derivedSeries_le_map_derivedSeries hsurjective index
  rw [Group.IsPerfect.derivedSeries_eq_top, ← hindex] at himage
  exact top_le_iff.mp himage

theorem normalizer_le_normalizer_characteristic_map
    {G : Type*} [Group G] (overgroup : Subgroup G) (internalGroup : Subgroup overgroup)
    (hcharacteristic : internalGroup.Characteristic) :
    Subgroup.normalizer (overgroup : Set G) ≤
      Subgroup.normalizer (Subgroup.map overgroup.subtype internalGroup : Set G) := by
  intro element helement
  let normalizingElement : Subgroup.normalizer (overgroup : Set G) := ⟨element, helement⟩
  let automorphism := overgroup.normalizerMonoidHom normalizingElement
  have hpreserves := Subgroup.characteristic_iff_map_eq.mp hcharacteristic automorphism
  have hhom : (MulAut.conj element).toMonoidHom.comp overgroup.subtype =
      overgroup.subtype.comp automorphism.toMonoidHom := by
    ext value
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe overgroup normalizingElement value).symm
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  change Subgroup.map (MulAut.conj element).toMonoidHom
    (Subgroup.map overgroup.subtype internalGroup) = _
  rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hpreserves]

@[expose] def perfectResidualOf {G : Type*} [Group G] (overgroup : Subgroup G) : Subgroup G :=
  Subgroup.map overgroup.subtype (perfectResidual overgroup)

theorem perfectResidualOf_normalizer_contains
    {G : Type*} [Group G] (overgroup : Subgroup G) :
    Subgroup.normalizer (overgroup : Set G) ≤
      Subgroup.normalizer (perfectResidualOf overgroup : Set G) :=
  normalizer_le_normalizer_characteristic_map overgroup (perfectResidual overgroup)
    perfectResidual_characteristic

theorem finite_perfectResidualOf_isPerfect
    {G : Type*} [Group G] [Finite G] (overgroup : Subgroup G) :
    Group.IsPerfect (perfectResidualOf overgroup) := by
  have hinternal := finite_perfectResidual_isPerfect (G := overgroup)
  apply Subgroup.isPerfect_iff.mpr
  unfold perfectResidualOf
  rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hinternal]

theorem normalizer_preimage_le_normalizer_perfectResidualOf
    {G Image : Type*} [Group G] [Group Image] (homomorphism : G →* Image)
    (imageGroup : Subgroup Image) :
    Subgroup.comap homomorphism (Subgroup.normalizer (imageGroup : Set Image)) ≤
      Subgroup.normalizer (perfectResidualOf (Subgroup.comap homomorphism imageGroup) : Set G) := by
  apply le_trans _ (perfectResidualOf_normalizer_contains _)
  intro element helement
  apply Subgroup.mem_normalizer_iff.mpr
  intro value
  change homomorphism value ∈ imageGroup ↔
    homomorphism (element * value * element⁻¹) ∈ imageGroup
  simpa only [map_mul, map_inv] using
    Subgroup.mem_normalizer_iff.mp helement (homomorphism value)

end CFSG.RankThreeCoreUniqueness.Helpers
