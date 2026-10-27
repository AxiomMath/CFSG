module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassURank
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassUF3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section General

variable {G : Type*} [Group G]

theorem commutator_subgroupOf_eq_of_le {C A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    ⁅A.subgroupOf C, B.subgroupOf C⁆ = (⁅A, B⁆).subgroupOf C := by
  apply map_injective C.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB,
    map_subgroupOf_eq_of_le ((commutator_mono hA hB).trans (commutator_le_self C))]

theorem map_conj_subgroupOf_eq_iff {C H : Subgroup G} (hH : H ≤ C) (g : C) :
    (H.subgroupOf C).map (MulAut.conj g).toMonoidHom = H.subgroupOf C ↔
      (g : G) ∈ normalizer (H : Set G) := by
  refine (mem_normalizer_iff_map_conj_eq (H := H.subgroupOf C) (g := g)).symm.trans ?_
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h y
    constructor
    · intro hy
      have := (h ⟨y, hH hy⟩).1 (mem_subgroupOf.2 hy)
      simpa [mem_subgroupOf] using this
    · intro hy
      have hyC : y ∈ C := by
        have h1 : (g : G) * y * (g : G)⁻¹ ∈ C := hH hy
        have h2 : y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by group
        rw [h2]
        exact mul_mem (mul_mem (inv_mem g.2) h1) g.2
      have := (h ⟨y, hyC⟩).2 (by simpa [mem_subgroupOf] using hy)
      simpa [mem_subgroupOf] using this
  · intro h y
    rw [mem_subgroupOf, mem_subgroupOf]
    simpa using h y

end General

variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def uRootGroup : Subgroup (adjointGroup .E7 K) :=
  ((rootSubgroup .E7 K uTopRoot).subgroupOf (adjointGroup .E7 K)).map
    (MulAut.conj (e7RepConj K 3)).toMonoidHom

variable (K) in
@[expose] def leviURootSubgroups : Set (Subgroup (adjointGroup .E7 K)) :=
  {X | ∃ c ∈ leviU K, X = (uRootGroup K).map (MulAut.conj c).toMonoidHom}

theorem uTopGroup_le_adjointGroup : uTopGroup K ≤ adjointGroup .E7 K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem radicalU_eq_map_conj {c : adjointGroup .E7 K} (hc : c ∈ leviU K) :
    radicalU K = ((parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K)).map
      (MulAut.conj (c * e7RepConj K 3)).toMonoidHom := by
  rw [← CFSG.LieType.Chevalley.map_conj_map_conj]
  exact (mem_normalizer_iff_map_conj_eq.1 (leviU_le_normalizer_radicalU hc)).symm

theorem commutator_radicalU_leviURootSubgroup [CharP K 2] {c : adjointGroup .E7 K}
    (hc : c ∈ leviU K) :
    ⁅radicalU K, (uRootGroup K).map (MulAut.conj c).toMonoidHom⁆ =
      ((uTopGroup K).subgroupOf (adjointGroup .E7 K)).map
        (MulAut.conj (c * e7RepConj K 3)).toMonoidHom := by
  rw [radicalU_eq_map_conj hc, uRootGroup, CFSG.LieType.Chevalley.map_conj_map_conj, ← map_commutator,
    commutator_subgroupOf_eq_of_le
      ((parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup)
      (rootSubgroup_le_adjointGroup _),
    commutator_parabolicRadical_rootSubgroup_uTopRoot]

theorem rootSubgroup_eq_of_commutator_eq [CharP K 2] {X X' : Subgroup (adjointGroup .E7 K)}
    (hX : X ∈ leviURootSubgroups K) (hX' : X' ∈ leviURootSubgroups K)
    (h : ⁅radicalU K, X⁆ = ⁅radicalU K, X'⁆) : X = X' := by
  obtain ⟨c, hc, rfl⟩ := hX
  obtain ⟨c', hc', rfl⟩ := hX'
  set n := e7RepConj K 3 with hn
  rw [commutator_radicalU_leviURootSubgroup hc, commutator_radicalU_leviURootSubgroup hc'] at h
  set T := (uTopGroup K).subgroupOf (adjointGroup .E7 K) with hT
  set U := (rootSubgroup .E7 K uTopRoot).subgroupOf (adjointGroup .E7 K) with hU
  set g := (c * n)⁻¹ * (c' * n) with hg
  have hgT : T.map (MulAut.conj g).toMonoidHom = T := by
    rw [hg, ← CFSG.LieType.Chevalley.map_conj_map_conj, ← h, CFSG.LieType.Chevalley.map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hgM : (g : ModGL .E7 K) ∈ parabolicLevi .E7 K uNodes := by
    obtain ⟨m, hm, hmc⟩ := hc
    obtain ⟨m', hm', hmc'⟩ := hc'
    have e : g = m⁻¹ * m' := by
      rw [hg, ← hmc, ← hmc', hn]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact mem_subgroupOf.1 (mul_mem (inv_mem hm) hm')
  have hgN : (g : ModGL .E7 K) ∈ normalizer (uTopGroup K : Set (ModGL .E7 K)) :=
    (map_conj_subgroupOf_eq_iff uTopGroup_le_adjointGroup g).1 hgT
  have hgU : U.map (MulAut.conj g).toMonoidHom = U :=
    (map_conj_subgroupOf_eq_iff (rootSubgroup_le_adjointGroup _) g).2
      (mem_normalizer_rootSubgroup_of_mem_normalizer_uTopGroup g.2 hgM hgN)
  have e : c' * n = (c * n) * g := by rw [hg]; group
  calc (uRootGroup K).map (MulAut.conj c).toMonoidHom = U.map (MulAut.conj (c * n)).toMonoidHom := by
        rw [uRootGroup, CFSG.LieType.Chevalley.map_conj_map_conj]
    _ = (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (c * n)).toMonoidHom := by rw [hgU]
    _ = U.map (MulAut.conj (c * n * g)).toMonoidHom := by
        rw [CFSG.LieType.Chevalley.map_conj_map_conj]
    _ = U.map (MulAut.conj (c' * n)).toMonoidHom := by rw [e]
    _ = (uRootGroup K).map (MulAut.conj c').toMonoidHom := by
        rw [uRootGroup, CFSG.LieType.Chevalley.map_conj_map_conj]

theorem commutator_radicalU_zpowers_eq [CharP K 2] {X : Subgroup (adjointGroup .E7 K)}
    (hX : X ∈ leviURootSubgroups K) {x : adjointGroup .E7 K} (hx : x ∈ X) (hx1 : x ≠ 1) :
    ⁅radicalU K, zpowers x⁆ = ⁅radicalU K, X⁆ := by
  obtain ⟨c, hc, rfl⟩ := hX
  rw [commutator_radicalU_leviURootSubgroup hc]
  set n := e7RepConj K 3
  rw [uRootGroup, CFSG.LieType.Chevalley.map_conj_map_conj] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : (y : ModGL .E7 K) ≠ 1 := by
    intro h1
    apply hx1
    have : y = 1 := Subtype.ext h1
    rw [this, map_one]
  have hQC : parabolicRadical .E7 K uNodes ≤ adjointGroup .E7 K :=
    (parabolicRadical_le_posUnipotent _).trans posUnipotent_le_adjointGroup
  have key : ⁅(parabolicRadical .E7 K uNodes).subgroupOf (adjointGroup .E7 K), zpowers y⁆ =
      (uTopGroup K).subgroupOf (adjointGroup .E7 K) := by
    apply map_injective (adjointGroup .E7 K).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hQC, MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le uTopGroup_le_adjointGroup]
    exact commutator_parabolicRadical_zpowers_eq (mem_subgroupOf.1 hy) hy1
  rw [radicalU_eq_map_conj hc, ← MonoidHom.map_zpowers, ← map_commutator, key]

end CFSG.SeitzReduction.E7Pilot
