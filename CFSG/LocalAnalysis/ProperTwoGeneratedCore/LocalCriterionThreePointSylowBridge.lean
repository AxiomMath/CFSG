module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylowCounting

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

open CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

variable {G : Type*} [Group G]

theorem sylow_subgroupOf_restriction_ambient_image [Finite G]
    (p : ℕ) (hp : p.Prime) (B K : Subgroup G) (hBK : B ≤ K)
    (P : Sylow p B) :
    ∃ Q : Sylow p (B.subgroupOf K),
      ((Q : Subgroup (B.subgroupOf K)).map (B.subgroupOf K).subtype).map K.subtype =
        (P : Subgroup B).map B.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let e : B.subgroupOf K ≃* B := Subgroup.subgroupOfEquivOfLe hBK
  let f : B.subgroupOf K →* B := e.toMonoidHom
  have hf : Function.Surjective f := by
    intro b
    refine ⟨e.symm b, ?_⟩
    change e (e.symm b) = b
    exact e.apply_symm_apply b
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective (f := f) hf p P
  refine ⟨Q, ?_⟩
  rw [← hQ]
  change ((Q : Subgroup (B.subgroupOf K)).map (B.subgroupOf K).subtype).map K.subtype =
    ((Q : Subgroup (B.subgroupOf K)).map f).map B.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  have hhom : K.subtype.comp (B.subgroupOf K).subtype = B.subtype.comp f := by
    ext a
    exact (Subgroup.subgroupOfEquivOfLe_apply_coe hBK a).symm
  rw [hhom]

theorem sylow_subgroupOf_extension_ambient_image [Finite G]
    (p : ℕ) (hp : p.Prime) (B K : Subgroup G) (hBK : B ≤ K)
    (Q : Sylow p (B.subgroupOf K)) :
    ∃ P : Sylow p B,
      (P : Subgroup B).map B.subtype =
        ((Q : Subgroup (B.subgroupOf K)).map (B.subgroupOf K).subtype).map K.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let e : B.subgroupOf K ≃* B := Subgroup.subgroupOfEquivOfLe hBK
  let f : B.subgroupOf K →* B := e.toMonoidHom
  have hf : Function.Surjective f := by
    intro b
    refine ⟨e.symm b, ?_⟩
    change e (e.symm b) = b
    exact e.apply_symm_apply b
  refine ⟨Q.mapSurjective (f := f) hf, ?_⟩
  change ((Q : Subgroup (B.subgroupOf K)).map f).map B.subtype =
    ((Q : Subgroup (B.subgroupOf K)).map (B.subgroupOf K).subtype).map K.subtype
  rw [Subgroup.map_map, Subgroup.map_map]
  have hhom : K.subtype.comp (B.subgroupOf K).subtype = B.subtype.comp f := by
    ext a
    exact (Subgroup.subgroupOfEquivOfLe_apply_coe hBK a).symm
  rw [hhom]

theorem centralizer_in_subgroup_eq_ambient_restriction
    (K : Subgroup G) (t : K) :
    Subgroup.centralizer ({t} : Set K) =
      (Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf K := by
  ext a
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem normalizer_in_subgroup_iff_ambient_image
    (K : Subgroup G) (U : Subgroup K) (t : K) :
    t ∈ Subgroup.normalizer (U : Set K) ↔
      (t : G) ∈ Subgroup.normalizer ((U.map K.subtype : Subgroup G) : Set G) := by
  constructor
  · intro ht
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem K.subtype ht)
  · intro ht
    have h := Subgroup.le_normalizer_comap K.subtype ht
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective U] at h
    exact h

theorem conjugacyWithin_ambient_image_card_eq_internal_relIndex
    (K : Subgroup G) (U : Subgroup K) (t : K) :
    Nat.card (conjugacyWithin (U.map K.subtype) (t : G)) =
      (Subgroup.centralizer ({t} : Set K)).relIndex U := by
  rw [conjugacyWithin_card_eq_centralizer_index]
  change (Subgroup.centralizer ({(t : G)} : Set G)).relIndex (U.map K.subtype) = _
  rw [← Subgroup.relIndex_comap]
  change ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf K).relIndex U = _
  rw [← centralizer_in_subgroup_eq_ambient_restriction]

end CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
