module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem Sec5Setting.isOm6Z2 [Finite G] {t : G} {L : Subgroup G} (h : Sec5Setting G t L) :
    IsOm6Z2 L :=
  ⟨h.component.isQuasisimple, h.twoU43⟩

theorem sec5_isCyclic_of_isSylow2Of [Finite G] {H : Subgroup G}
    (hcyc : ∀ P : Sylow 2 ↥H, IsCyclic (P : Subgroup ↥H)) {P : Subgroup G}
    (hP : IsSylow2Of P H) : IsCyclic ↥P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow
  haveI : IsCyclic ↥(Q : Subgroup ↥H) := hcyc Q
  rw [← hQ]
  exact isCyclic_of_surjective
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥H) H.subtype H.subtype_injective).toMonoidHom
    (Subgroup.equivMapOfInjective (Q : Subgroup ↥H) H.subtype H.subtype_injective).surjective

theorem sec5_mem_centerIn_iff {X : Subgroup G} {x : G} :
    x ∈ centerIn X ↔ x ∈ X ∧ ∀ y ∈ X, x * y = y * x := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
    exact (h g g.2).symm

theorem sec5_layerCent_of_mem_centralizer [Finite G] {L : Subgroup G} (hL : IsQuasisimple L)
    {s : G} (hs : s ∈ centralizer (L : Set G)) : layerCent L s = L := by
  have hs' : ∀ x ∈ L, x * s = s * x := fun x hx => Subgroup.mem_centralizer_iff.mp hs x hx
  have hinf : L ⊓ centralizer ({s} : Set G) = L := by
    rw [inf_eq_left]
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hs' x hx
  have htop : IsComponent (⊤ : Subgroup ↥L) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hL, Subgroup.IsSubnormal.top⟩
  have hlayer : CFSG.layer ↥L = ⊤ := by
    rw [CFSG.layer.eq_sSup]
    exact top_le_iff.mp (le_sSup htop)
  have hin : CFSG.inSubgroup CFSG.layer L = L := by
    unfold CFSG.inSubgroup
    rw [hlayer, Subgroup.map_top, Subgroup.range_subtype]
  rw [layerCent, hinf, hin]

theorem sec5_layerCent_ne_bot_of_mem_centralizer [Finite G] {L : Subgroup G}
    (hL : IsQuasisimple L) {s : G} (hs : s ∈ centralizer (L : Set G)) : layerCent L s ≠ ⊥ := by
  rw [sec5_layerCent_of_mem_centralizer hL hs]
  intro hbot
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hL
  rw [hbot] at hnt
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hnt

theorem sec5_isI4PlusIn_conj {L : Subgroup G} {z c : G} (h : IsI4PlusIn L z)
    (hc : c ∈ normalizer (L : Set G)) : IsI4PlusIn L (c * z * c⁻¹) := by
  have h1 := h.conjugate c⁻¹
  have h2 : CFSG.conjugate L c⁻¹ = L := by
    ext x
    rw [mem_conjugate_iff]
    exact (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem hc) x).symm
  rwa [h2, inv_inv] at h1

end CFSG.OddStandard.SmallF3.Omega
