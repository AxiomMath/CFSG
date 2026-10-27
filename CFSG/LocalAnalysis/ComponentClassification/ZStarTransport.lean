module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionZStarEscape

public section

open CFSG.Open

namespace CFSG.ComponentClassification.ZStarTransport

theorem center_map {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H) :
    (Subgroup.center G).map equivalence.toMonoidHom = Subgroup.center H := by
  ext member
  constructor
  · rintro ⟨lift, hlift, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro other
    obtain ⟨original, rfl⟩ := equivalence.surjective other
    change equivalence original * equivalence lift = equivalence lift * equivalence original
    rw [← map_mul, ← map_mul]
    exact congrArg equivalence (Subgroup.mem_center_iff.mp hlift original)
  · intro hmember
    refine ⟨equivalence.symm member, Subgroup.mem_center_iff.mpr ?_, equivalence.apply_symm_apply member⟩
    intro other
    apply equivalence.injective
    rw [map_mul, map_mul, equivalence.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hmember (equivalence other)

theorem mapped_center {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (subgroup : Subgroup G) :
    ((Subgroup.center subgroup).map subgroup.subtype).map equivalence.toMonoidHom =
      (Subgroup.center (subgroup.map equivalence.toMonoidHom)).map (subgroup.map equivalence.toMonoidHom).subtype := by
  let restriction := subgroup.equivMapOfInjective equivalence.toMonoidHom equivalence.injective
  have hcenter := congrArg (Subgroup.map (subgroup.map equivalence.toMonoidHom).subtype) (center_map restriction)
  rw [Subgroup.map_map] at hcenter
  have hhom : (subgroup.map equivalence.toMonoidHom).subtype.comp restriction.toMonoidHom =
      equivalence.toMonoidHom.comp subgroup.subtype := by
    ext member
    rfl
  rw [hhom, ← Subgroup.map_map] at hcenter
  exact hcenter

theorem equiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (equivalence : G ≃* H) (hzstar : TwoActionZStarEscape.ZStar G) : TwoActionZStarEscape.ZStar H := by
  intro sylow element horder hcenter hisolated
  have hsurjective : Function.Surjective equivalence.symm.toMonoidHom := equivalence.symm.surjective
  let transported := sylow.mapSurjective (f := equivalence.symm.toMonoidHom) hsurjective
  have htransported : (transported : Subgroup G) = (sylow : Subgroup H).map equivalence.symm.toMonoidHom :=
    Sylow.coe_mapSurjective hsurjective sylow
  have hcenterBack : equivalence.symm element ∈
      (Subgroup.center (transported : Subgroup G)).map (transported : Subgroup G).subtype := by
    have hmap := Subgroup.mem_map_of_mem equivalence.symm.toMonoidHom hcenter
    rw [mapped_center, ← htransported] at hmap
    exact hmap
  have horderBack : orderOf (equivalence.symm element) = 2 :=
    (orderOf_injective equivalence.symm.toMonoidHom equivalence.symm.injective element).trans horder
  have hisolatedBack : ∀ actor : G, actor * equivalence.symm element * actor⁻¹ ∈ (transported : Subgroup G) →
      actor * equivalence.symm element * actor⁻¹ = equivalence.symm element := by
    intro actor hactor
    have hmap : equivalence (actor * equivalence.symm element * actor⁻¹) ∈ (sylow : Subgroup H) := by
      rw [htransported, Subgroup.mem_map_equiv] at hactor
      exact hactor
    rw [map_mul, map_mul, map_inv, equivalence.apply_symm_apply] at hmap
    apply equivalence.injective
    rw [map_mul, map_mul, map_inv, equivalence.apply_symm_apply]
    exact hisolated (equivalence actor) hmap
  have hconclusion := hzstar transported (equivalence.symm element) horderBack hcenterBack hisolatedBack
  have hmap := congrArg (Subgroup.map equivalence.toMonoidHom) hconclusion
  rw [Subgroup.map_sup, UniversalComponentBlock.singleton_centralizer_map, equivalence.apply_symm_apply,
    OddCore.equiv_invariant equivalence] at hmap
  have htop : (⊤ : Subgroup G).map equivalence.toMonoidHom = ⊤ := by
    apply le_antisymm le_top
    intro member _
    exact Subgroup.mem_map.mpr ⟨equivalence.symm member, Subgroup.mem_top _, equivalence.apply_symm_apply member⟩
  exact hmap.trans htop

theorem subgroup_of_quotients {G : Type*} [Group G] [Finite G]
    (hquotient : ∀ subgroup : Subgroup G, ∀ normal : Subgroup subgroup, ∀ hnormal : normal.Normal,
      letI := hnormal
      TwoActionZStarEscape.ZStar (subgroup ⧸ normal)) :
    ∀ subgroup : Subgroup G, TwoActionZStarEscape.ZStar subgroup := by
  intro subgroup
  exact equiv (QuotientGroup.quotientBot (G := subgroup)) (hquotient subgroup ⊥ inferInstance)

end CFSG.ComponentClassification.ZStarTransport
