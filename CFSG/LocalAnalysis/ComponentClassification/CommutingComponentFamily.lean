module

public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CommutingComponentFamily

@[expose] noncomputable def generated {G : Type*} [Group G] (family : Set (Subgroup G)) : Subgroup G :=
  sSup family

theorem factor_le {G : Type*} [Group G] (family : Set (Subgroup G))
    (factor : Subgroup G) (hfactor : factor ∈ family) : factor ≤ generated family :=
  le_sSup hfactor

theorem factor_normal {G : Type*} [Group G] (family : Set (Subgroup G))
    (hcommutes : ∀ first ∈ family, ∀ second ∈ family, first ≠ second → ⁅first, second⁆ = ⊥)
    (factor : Subgroup G) (hfactor : factor ∈ family) :
    (factor.subgroupOf (generated family)).Normal := by
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  apply sSup_le
  intro other hother
  by_cases heq : other = factor
  · rw [heq]
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (hcommutes other hother factor hfactor heq)).trans (Subgroup.centralizer_le_normalizer _)

theorem factor_component {G : Type*} [Group G] (family : Set (Subgroup G))
    (hcommutes : ∀ first ∈ family, ∀ second ∈ family, first ≠ second → ⁅first, second⁆ = ⊥)
    (hquasisimple : ∀ factor ∈ family, IsQuasisimple factor)
    (factor : Subgroup G) (hfactor : factor ∈ family) :
    IsComponentOf (factor.subgroupOf (generated family)) ⊤ := by
  let : (factor.subgroupOf (generated family)).Normal := factor_normal family hcommutes factor hfactor
  exact (OrdinaryComponentTransport.subgroupOf_iff factor (generated family)
    (factor_le family factor hfactor)).mpr
    ⟨(inferInstance : (factor.subgroupOf (generated family)).Normal).isSubnormal,
      hquasisimple factor hfactor⟩

theorem perfect {G : Type*} [Group G] (family : Set (Subgroup G))
    (hperfect : ∀ factor ∈ family, Group.IsPerfect factor) :
    Group.IsPerfect (generated family) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _) _
  apply sSup_le
  intro factor hfactor
  let : Group.IsPerfect factor := hperfect factor hfactor
  rw [← Subgroup.commutator_eq_self (H := factor)]
  exact Subgroup.commutator_mono (factor_le family factor hfactor) (factor_le family factor hfactor)

theorem components_exact {G : Type*} [Group G] [Finite G] (family : Set (Subgroup G))
    (hcommutes : ∀ first ∈ family, ∀ second ∈ family, first ≠ second → ⁅first, second⁆ = ⊥)
    (hquasisimple : ∀ factor ∈ family, IsQuasisimple factor)
    (component : Subgroup G) (hcomponentLe : component ≤ generated family) :
    IsComponentOf (component.subgroupOf (generated family)) ⊤ ↔ component ∈ family := by
  constructor
  · intro hcomponent
    by_contra hnot
    have hcentralizes : generated family ≤ Subgroup.centralizer (component : Set G) := by
      apply sSup_le
      intro factor hfactor
      have hne : factor ≠ component := by
        intro heq
        exact hnot (heq ▸ hfactor)
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (OrdinaryComponentTransport.commute_local_distinct factor component (generated family)
          (factor_le family factor hfactor) hcomponentLe
          (factor_component family hcommutes hquasisimple factor hfactor) hcomponent hne)
    have hcentral : component.subgroupOf (generated family) ≤
        Subgroup.center (generated family) := by
      intro member hmember
      apply Subgroup.mem_center_iff.mpr
      intro other
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp
        (hcentralizes other.property) member.val hmember).symm
    let : Group.IsPerfect (component.subgroupOf (generated family)) := ⟨hcomponent.2.2.1⟩
    have hbot := Quasisimple.perfect_le_center_eq_bot _ hcentral
    exact ((component.subgroupOf (generated family)).nontrivial_iff_ne_bot.mp
      (Quasisimple.nontrivial hcomponent.2.2)) hbot
  · exact factor_component family hcommutes hquasisimple component

theorem normalizer_iff_conjugate_eq {G : Type*} [Group G]
    (subgroup : Subgroup G) (actor : G) :
    actor ∈ Subgroup.normalizer (subgroup : Set G) ↔
      subgroup.map (MulAut.conj actor).toMonoidHom = subgroup := by
  constructor
  · intro hnormalizes
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hnormalizes lift).mp hlift
    · intro hmember
      refine ⟨(MulAut.conj actor).symm member, ?_, (MulAut.conj actor).apply_symm_apply member⟩
      apply (Subgroup.mem_normalizer_iff.mp hnormalizes _).mpr
      change (MulAut.conj actor) ((MulAut.conj actor).symm member) ∈ subgroup
      rwa [(MulAut.conj actor).apply_symm_apply]
  · intro heq
    apply Subgroup.mem_normalizer_iff.mpr
    intro member
    constructor
    · intro hmember
      rw [← heq]
      exact Subgroup.mem_map_of_mem (MulAut.conj actor).toMonoidHom hmember
    · intro hmember
      have hmap : (MulAut.conj actor) member ∈ subgroup.map (MulAut.conj actor).toMonoidHom := by
        rwa [heq]
      rw [Subgroup.mem_map_equiv] at hmap
      rwa [(MulAut.conj actor).symm_apply_apply] at hmap

theorem map_generated_le {G H : Type*} [Group G] [Group H]
    (equivalence : G ≃* H) (family : Set (Subgroup G)) (targetFamily : Set (Subgroup H))
    (hpreserves : ∀ factor ∈ family, factor.map equivalence.toMonoidHom ∈ targetFamily) :
    (generated family).map equivalence.toMonoidHom ≤ generated targetFamily := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro factor hfactor
  exact Subgroup.map_le_iff_le_comap.mp (factor_le targetFamily _ (hpreserves factor hfactor))

theorem normalizer_iff_preserves_family {G : Type*} [Group G] [Finite G]
    (family : Set (Subgroup G))
    (hcommutes : ∀ first ∈ family, ∀ second ∈ family, first ≠ second → ⁅first, second⁆ = ⊥)
    (hquasisimple : ∀ factor ∈ family, IsQuasisimple factor) (actor : G) :
    actor ∈ Subgroup.normalizer (generated family : Set G) ↔
      ∀ factor ∈ family, factor.map (MulAut.conj actor).toMonoidHom ∈ family := by
  rw [normalizer_iff_conjugate_eq]
  constructor
  · intro hgenerated factor hfactor
    have hle := Subgroup.map_mono (f := (MulAut.conj actor).toMonoidHom)
      (factor_le family factor hfactor)
    rw [hgenerated] at hle
    apply (components_exact family hcommutes hquasisimple _ hle).mp
    have hcomponent := OrdinaryComponentTransport.map_nested (MulAut.conj actor) factor
      (generated family) (factor_component family hcommutes hquasisimple factor hfactor)
    rwa [hgenerated] at hcomponent
  · intro hpreserves
    apply Subgroup.eq_of_le_of_card_ge (map_generated_le (MulAut.conj actor) family family hpreserves)
    rw [Subgroup.card_map_of_injective (MulAut.conj actor).injective]

theorem factor_component_normalizer {G : Type*} [Group G] (family : Set (Subgroup G))
    (hcommutes : ∀ first ∈ family, ∀ second ∈ family, first ≠ second → ⁅first, second⁆ = ⊥)
    (hquasisimple : ∀ factor ∈ family, IsQuasisimple factor)
    (factor : Subgroup G) (hfactor : factor ∈ family) :
    IsComponentOf (factor.subgroupOf (Subgroup.normalizer (generated family : Set G))) ⊤ := by
  apply OrdinaryComponentTransport.extend_nested factor (generated family) _
    (factor_le family factor hfactor) Subgroup.le_normalizer
  · exact (inferInstance : ((generated family).subgroupOf
      (Subgroup.normalizer (generated family : Set G))).Normal).isSubnormal
  · exact factor_component family hcommutes hquasisimple factor hfactor

end CFSG.ComponentClassification.CommutingComponentFamily
