module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem normalizer_normalizes_normalizer {G : Type u} [Group G] (subgroup : Subgroup G) :
    Subgroup.normalizer (subgroup : Set G) ≤
      Subgroup.normalizer (Subgroup.normalizer (subgroup : Set G) : Set G) := Subgroup.le_normalizer

theorem pSubgroup_sylow_of_sylow_in_normalizer {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G) (hpgroup : IsPGroup prime subgroup)
    (hmaximal : ∀ larger : Subgroup G, larger ≤ Subgroup.normalizer (subgroup : Set G) →
      IsPGroup prime larger → subgroup ≤ larger → larger = subgroup) :
    ∃ sylow : Sylow prime G, (sylow : Subgroup G) = subgroup := by
  obtain ⟨sylow, hle⟩ := hpgroup.exists_le_sylow
  have hrestrictedPGroup : IsPGroup prime (subgroup.subgroupOf (sylow : Subgroup G)) := by
    let equivalence := Subgroup.subgroupOfEquivOfLe hle
    exact hpgroup.of_injective equivalence.toMonoidHom equivalence.injective
  have hnormalizerPGroup : IsPGroup prime
      (Subgroup.normalizer (subgroup : Set G) ⊓ (sylow : Subgroup G) : Subgroup G) :=
    sylow.isPGroup'.of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  have hnormalizerEq := hmaximal _ inf_le_left hnormalizerPGroup
    (le_inf Subgroup.le_normalizer hle)
  have hinternalNormalizer : Subgroup.normalizer
      (subgroup.subgroupOf (sylow : Subgroup G) : Set (sylow : Subgroup G)) =
        subgroup.subgroupOf (sylow : Subgroup G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hle]
    have heq : (Subgroup.normalizer (subgroup : Set G)).subgroupOf (sylow : Subgroup G) =
        (Subgroup.normalizer (subgroup : Set G) ⊓ (sylow : Subgroup G)).subgroupOf
          (sylow : Subgroup G) := by
      ext element
      exact ⟨fun hmem => ⟨hmem, element.property⟩, fun hmem => hmem.1⟩
    rw [heq, hnormalizerEq]
  have : Fact prime.Prime := ⟨hprime⟩
  have : Group.IsNilpotent (sylow : Subgroup G) := sylow.isPGroup'.isNilpotent
  have htop := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := (sylow : Subgroup G))))
      (subgroup.subgroupOf (sylow : Subgroup G)) hinternalNormalizer
  have hreverse : (sylow : Subgroup G) ≤ subgroup := by
    intro element helement
    have hmem : (⟨element, helement⟩ : (sylow : Subgroup G)) ∈
        subgroup.subgroupOf (sylow : Subgroup G) := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hmem
  exact ⟨sylow, le_antisymm hreverse hle⟩

theorem exists_normalized_sylow_containing_normalized_pSubgroup
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (sylowPrime : ℕ) (hsylowPrime : sylowPrime.Prime)
    (actor overgroup subgroup : Subgroup G) (hpgroup : IsPGroup prime actor)
    (hcomplement : ¬prime ∣ Nat.card overgroup)
    (hovergroupNormalized : actor ≤ Subgroup.normalizer (overgroup : Set G))
    (hsubgroupLe : subgroup ≤ overgroup) (hsubgroupPGroup : IsPGroup sylowPrime subgroup)
    (hsubgroupNormalized : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    ∃ sylow : Sylow sylowPrime overgroup,
      subgroup ≤ (sylow : Subgroup overgroup).map overgroup.subtype ∧
        actor ≤ Subgroup.normalizer (((sylow : Subgroup overgroup).map overgroup.subtype) : Set G) := by
  have : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
  obtain ⟨maximal, hsubgroupMaximal, hmaximal⟩ := Finite.exists_le_maximal
    (p := fun candidate : Subgroup G => candidate ≤ overgroup ∧ IsPGroup sylowPrime candidate ∧
      actor ≤ Subgroup.normalizer (candidate : Set G))
      ⟨hsubgroupLe, hsubgroupPGroup, hsubgroupNormalized⟩
  let normalizer := overgroup ⊓ Subgroup.normalizer (maximal : Set G)
  have hmaximalNormalizer : maximal ≤ normalizer := le_inf hmaximal.1.1 Subgroup.le_normalizer
  have hnormalizerNormalized : actor ≤ Subgroup.normalizer (normalizer : Set G) :=
    normalizes_inf_of_normalizes_both actor overgroup _ hovergroupNormalized
      (hmaximal.1.2.2.trans (normalizer_normalizes_normalizer maximal))
  have hnormalizerComplement : ¬prime ∣ Nat.card normalizer :=
    fun hdiv => hcomplement (hdiv.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨normalizerSylow, hnormalizerSylowNormalized⟩ :=
    exists_normalized_sylow_in_prime_complement_subgroup prime hprime actor normalizer hpgroup
      hnormalizerComplement hnormalizerNormalized sylowPrime hsylowPrime
  let ambientSylow := (normalizerSylow : Subgroup normalizer).map normalizer.subtype
  have hrestrictedNormal : (maximal.subgroupOf normalizer).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hmaximalNormalizer).mpr inf_le_right
  have : (maximal.subgroupOf normalizer).Normal := hrestrictedNormal
  have hrestrictedPGroup : IsPGroup sylowPrime (maximal.subgroupOf normalizer) := by
    let equivalence := Subgroup.subgroupOfEquivOfLe hmaximalNormalizer
    exact hmaximal.1.2.1.of_injective equivalence.toMonoidHom equivalence.injective
  have hmaximalSylowLe : maximal ≤ ambientSylow := by
    have hle := hrestrictedPGroup.le_sylow_of_normal normalizerSylow
    have hmapped := Subgroup.map_mono (f := normalizer.subtype) hle
    rw [Subgroup.map_subgroupOf_eq_of_le hmaximalNormalizer] at hmapped
    exact hmapped
  have hambientEq : ambientSylow = maximal :=
    (hmaximal.eq_of_le ⟨(Subgroup.map_subtype_le _).trans inf_le_left,
      normalizerSylow.isPGroup'.map normalizer.subtype, hnormalizerSylowNormalized⟩ hmaximalSylowLe).symm
  have hmaximalInNormalizer : ∀ larger : Subgroup overgroup,
      larger ≤ Subgroup.normalizer (maximal.subgroupOf overgroup : Set overgroup) →
        IsPGroup sylowPrime larger → maximal.subgroupOf overgroup ≤ larger →
          larger = maximal.subgroupOf overgroup := by
    intro larger hlargerNormalizer hlargerPGroup hmaximalLe
    have hlargerLe : larger.map overgroup.subtype ≤ normalizer := by
      apply le_inf (Subgroup.map_subtype_le _)
      intro element helement
      obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp helement
      have hinternal := hlargerNormalizer hpreimage
      rw [← Subgroup.subgroupOf_normalizer_eq hmaximal.1.1] at hinternal
      exact hinternal
    have hrestrictedLe : (larger.map overgroup.subtype).subgroupOf normalizer ≤
        (normalizerSylow : Subgroup normalizer) := by
      have hSylowEq : maximal.subgroupOf normalizer = (normalizerSylow : Subgroup normalizer) := by
        apply Subgroup.map_injective normalizer.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hmaximalNormalizer, ← hambientEq]
      have hrestrictedPGroup : IsPGroup sylowPrime ((larger.map overgroup.subtype).subgroupOf normalizer) :=
        (hlargerPGroup.map overgroup.subtype).of_injective
          (Subgroup.subgroupOfEquivOfLe hlargerLe).toMonoidHom
            (Subgroup.subgroupOfEquivOfLe hlargerLe).injective
      have hle : maximal.subgroupOf normalizer ≤ (larger.map overgroup.subtype).subgroupOf normalizer := by
        have hmapped := Subgroup.map_mono (f := overgroup.subtype) hmaximalLe
        rw [Subgroup.map_subgroupOf_eq_of_le hmaximal.1.1] at hmapped
        intro element helement
        exact hmapped helement
      rw [hSylowEq] at hle
      exact le_of_eq (normalizerSylow.is_maximal' hrestrictedPGroup hle)
    have hmapped := Subgroup.map_mono (f := normalizer.subtype) hrestrictedLe
    rw [Subgroup.map_subgroupOf_eq_of_le hlargerLe] at hmapped
    change larger.map overgroup.subtype ≤ ambientSylow at hmapped
    rw [hambientEq] at hmapped
    apply le_antisymm ?_ hmaximalLe
    intro element helement
    exact hmapped (Subgroup.mem_map_of_mem overgroup.subtype helement)
  have hmaximalRestrictedPGroup : IsPGroup sylowPrime (maximal.subgroupOf overgroup) :=
    hmaximal.1.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hmaximal.1.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hmaximal.1.1).injective
  obtain ⟨sylow, hsylow⟩ := pSubgroup_sylow_of_sylow_in_normalizer sylowPrime hsylowPrime
    (maximal.subgroupOf overgroup) hmaximalRestrictedPGroup hmaximalInNormalizer
  refine ⟨sylow, ?_, ?_⟩
  · rw [hsylow, Subgroup.map_subgroupOf_eq_of_le hmaximal.1.1]
    exact hsubgroupMaximal
  · rw [hsylow, Subgroup.map_subgroupOf_eq_of_le hmaximal.1.1]
    exact hmaximal.1.2.2

end CFSG.RankThreeEvenClassification.Helpers
