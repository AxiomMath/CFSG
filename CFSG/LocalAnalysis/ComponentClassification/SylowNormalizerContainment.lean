module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.SylowNormalizerContainment

theorem ambient {G : Type*} [Group G] [Finite G]
    (subgroup : Subgroup G) (sylow : Sylow 2 subgroup)
    (hnormalizer : Subgroup.normalizer (((sylow : Subgroup subgroup).map subgroup.subtype : Subgroup G) : Set G) ≤ subgroup) :
    ∃ ambient : Sylow 2 G, (ambient : Subgroup G) = (sylow : Subgroup subgroup).map subgroup.subtype := by
  let image := (sylow : Subgroup subgroup).map subgroup.subtype
  have himage : image ≤ subgroup := Subgroup.map_subtype_le _
  obtain ⟨ambient, hambient⟩ := (sylow.isPGroup'.map subgroup.subtype).exists_le_sylow
  let inside := image.subgroupOf (ambient : Subgroup G)
  let normalizer := Subgroup.normalizer (inside : Set (ambient : Subgroup G))
  let normalizerImage := normalizer.map (ambient : Subgroup G).subtype
  have hnormalizerImage : normalizerImage ≤ Subgroup.normalizer (image : Set G) := by
    rintro member ⟨lift, hlift, rfl⟩
    change lift ∈ Subgroup.normalizer ((image.subgroupOf (ambient : Subgroup G)) : Set (ambient : Subgroup G)) at hlift
    rw [← Subgroup.subgroupOf_normalizer_eq hambient] at hlift
    exact hlift
  have hnormalizerSubgroup : normalizerImage ≤ subgroup := hnormalizerImage.trans hnormalizer
  have hnormalizerTwo : IsPGroup 2 normalizerImage :=
    (ambient.isPGroup'.to_subgroup normalizer).map (ambient : Subgroup G).subtype
  have himageNormalizer : image ≤ normalizerImage := by
    intro member hmember
    exact Subgroup.mem_map.mpr ⟨⟨member, hambient hmember⟩,
      (Subgroup.le_normalizer : inside ≤ normalizer) hmember, rfl⟩
  have hlocalLe : (sylow : Subgroup subgroup) ≤ normalizerImage.subgroupOf subgroup := by
    intro member hmember
    exact himageNormalizer (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  have hmaximal := sylow.is_maximal' hnormalizerTwo.comap_subtype hlocalLe
  have hnormalizerLeImage : normalizerImage ≤ image := by
    intro member hmember
    have hlocal : (⟨member, hnormalizerSubgroup hmember⟩ : subgroup) ∈ (sylow : Subgroup subgroup) := by
      rw [← hmaximal]
      exact hmember
    exact Subgroup.mem_map.mpr ⟨⟨member, hnormalizerSubgroup hmember⟩, hlocal, rfl⟩
  have hnormalizerEq : normalizer = inside := by
    apply le_antisymm _ Subgroup.le_normalizer
    intro member hmember
    exact hnormalizerLeImage (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
  let : Group.IsNilpotent (ambient : Subgroup G) := ambient.isPGroup'.isNilpotent
  have htop : inside = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp Group.normalizerCondition_of_isNilpotent) inside hnormalizerEq
  have hreverse : (ambient : Subgroup G) ≤ image := Subgroup.subgroupOf_eq_top.mp htop
  exact ⟨ambient, le_antisymm hreverse hambient⟩

end CFSG.ComponentClassification.SylowNormalizerContainment
