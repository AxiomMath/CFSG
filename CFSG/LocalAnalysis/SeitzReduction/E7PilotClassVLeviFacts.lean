module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassVLevi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed
open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Chevalley.RootOps (isRootB isRootB_iff)

local instance e7ClassVLeviFactsNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

theorem e7A5Root_complete_check : ∀ k < Tag.E7.rootCertificate.roots.length,
    Tag.E7.rootCertificate.root k 1 = 0 → Tag.E7.rootCertificate.root k 6 = 0 →
      ∃ i : Fin 6, ∃ j : Fin 6, i ≠ j ∧ e7A5Root i j = Tag.E7.rootCertificate.root k := by
  decide +kernel

theorem e7A5Root_nodes_check : ∀ i j : Fin 6, e7A5Root i j 1 = 0 ∧ e7A5Root i j 6 = 0 := by
  decide +kernel

theorem e7A5Root_mem_parabolicRoots {i j : Fin 6} (hij : i ≠ j) :
    e7A5Root i j ∈ parabolicRoots .E7 vNodes := by
  refine ⟨isRoot_e7A5Root hij, fun m hm => ?_⟩
  simp only [vNodes, Set.mem_ofPred_eq, not_and_or, not_not] at hm
  rcases hm with rfl | rfl
  · exact (e7A5Root_nodes_check i j).1
  · exact (e7A5Root_nodes_check i j).2

theorem exists_e7A5Root_eq_of_mem_parabolicRoots {γ : Fin Tag.E7.rank → ℤ}
    (hγ : γ ∈ parabolicRoots .E7 vNodes) : ∃ i j : Fin 6, i ≠ j ∧ e7A5Root i j = γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ.1
  refine e7A5Root_complete_check k hk (hγ.2 1 ?_) (hγ.2 6 ?_)
  · simp [vNodes]
  · simp [vNodes]

variable {K : Type} [Field K]

variable [Finite K] [CharP K 2]

theorem range_slToAdjointE7 :
    (slToAdjointE7 K).range =
      (rootSpan .E7 K (parabolicRoots .E7 vNodes)).subgroupOf (adjointGroup .E7 K) := by
  refine le_antisymm ?_ ?_
  · rw [MonoidHom.range_eq_map,
      ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨⟨i, j, hij, c⟩, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf, Matrix.TransvectionStruct.toSpecialLinearGroup_mk,
      slToAdjointE7_transvection, coe_e7A5Elt]
    exact pinnedX_mem_rootSpan (e7A5Root_mem_parabolicRoots hij) c
  · intro g hg
    rw [mem_subgroupOf] at hg
    have hle : rootSpan .E7 K (parabolicRoots .E7 vNodes) ≤
        (slToAdjointE7 K).range.map (adjointGroup .E7 K).subtype := by
      refine iSup₂_le fun γ hγ => (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      obtain ⟨i, j, hij, rfl⟩ := exists_e7A5Root_eq_of_mem_parabolicRoots hγ
      exact ⟨_, ⟨Matrix.SpecialLinearGroup.transvection hij c, rfl⟩, by
        rw [slToAdjointE7_transvection]; rfl⟩
    obtain ⟨l, hl, hlg⟩ := hle hg
    rwa [show g = l from Subtype.ext hlg.symm]

theorem range_slToAdjointE7_le_parabolicLevi :
    (slToAdjointE7 K).range ≤ (parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K) := by
  rw [range_slToAdjointE7]
  have hle : rootSpan .E7 K (parabolicRoots .E7 vNodes) ≤ parabolicLevi .E7 K vNodes :=
    iSup₂_le fun γ hγ => F4Pilot.rootSubgroup_le_parabolicLevi (K := K) hγ
  intro g hg
  rw [mem_subgroupOf] at hg ⊢
  exact hle hg

theorem range_spToAdjointE7_le_parabolicLevi :
    (spToAdjointE7 K).range ≤ (parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K) := by
  rintro _ ⟨A, rfl⟩
  exact range_slToAdjointE7_le_parabolicLevi ⟨spToSL K A, rfl⟩

theorem vLevi_le_conj_parabolicLevi :
    vLevi K ≤ ((parabolicLevi .E7 K vNodes).subgroupOf (adjointGroup .E7 K)).map
      (MulAut.conj (e7RepConj K 4)).toMonoidHom :=
  Subgroup.map_mono range_spToAdjointE7_le_parabolicLevi

theorem map_spToAdjointE7_rootGroup_of_eq {γ : Fin 3 → ℤ}
    {r : TauCeti.GLSymplecticFin.RootSubgroupIndex 3} (hr : stdVec r = toStd 3 γ)
    {α : Fin Tag.E7.rank → ℤ}
    (h : ∀ c : K, ((spToAdjointE7 K (elt r c) : adjointGroup .E7 K) : ModGL .E7 K) =
      pinnedX .E7 K α c) :
    (CFSG.LieType.Universal.Symplectic.rootGroup 3 K γ).map
        ((adjointGroup .E7 K).subtype.comp (spToAdjointE7 K)) = rootSubgroup .E7 K α := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hy
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, h c]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  · intro hx
    rw [rootSubgroup_eq_range] at hx
    obtain ⟨c, rfl⟩ := hx
    refine ⟨elt r (Multiplicative.toAdd c), (mem_rootGroup_iff hr).2 ⟨_, rfl⟩, ?_⟩
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, h, pinnedHom_apply]

theorem map_spToAdjointE7_rootGroup_pos :
    (CFSG.LieType.Universal.Symplectic.rootGroup 3 K (Pi.single 2 1)).map
        ((adjointGroup .E7 K).subtype.comp (spToAdjointE7 K)) =
      rootSubgroup .E7 K (e7RepPreHigh 4) := by
  obtain ⟨h1, -, h3, h4⟩ := e7A5Root_alpha4
  refine map_spToAdjointE7_rootGroup_of_eq (stdVec_positiveLong_eq (k := (2 : Fin 3)) (by decide))
    fun c => ?_
  rw [spToAdjointE7_positiveLong, h3, h4, coe_e7A5Elt, h1]

theorem map_spToAdjointE7_rootGroup_neg :
    (CFSG.LieType.Universal.Symplectic.rootGroup 3 K (-Pi.single 2 1)).map
        ((adjointGroup .E7 K).subtype.comp (spToAdjointE7 K)) =
      rootSubgroup .E7 K (-e7RepPreHigh 4) := by
  obtain ⟨-, h2, h3, h4⟩ := e7A5Root_alpha4
  refine map_spToAdjointE7_rootGroup_of_eq (stdVec_negativeLong_eq (k := (2 : Fin 3)) (by decide))
    fun c => ?_
  rw [spToAdjointE7_negativeLong, h3, h4, coe_e7A5Elt, h2]

theorem map_vLeviEquiv_spRootSL2_coe :
    (F4Pilot.spRootSL2 3 K (Pi.single 2 1)).map
        ((adjointGroup .E7 K).subtype.comp ((vLevi K).subtype.comp (vLeviEquiv K).toMonoidHom)) =
      EPilot.highRootSL2 .E7 K := by
  have e : (adjointGroup .E7 K).subtype.comp ((vLevi K).subtype.comp (vLeviEquiv K).toMonoidHom) =
      (MulAut.conj (e7RepConj K 4 : ModGL .E7 K)).toMonoidHom.comp
        ((adjointGroup .E7 K).subtype.comp (spToAdjointE7 K)) := by
    ext A
    rfl
  rw [e, ← Subgroup.map_map, F4Pilot.spRootSL2, Subgroup.map_sup, map_spToAdjointE7_rootGroup_pos,
    map_spToAdjointE7_rootGroup_neg, map_conj_e7RepConj_rootSL2_preHigh]

theorem map_vLeviEquiv_spRootSL2 :
    (F4Pilot.spRootSL2 3 K (Pi.single 2 1)).map
        ((vLevi K).subtype.comp (vLeviEquiv K).toMonoidHom) =
      (EPilot.highRootSL2 .E7 K).subgroupOf (adjointGroup .E7 K) := by
  ext x
  rw [mem_subgroupOf, ← map_vLeviEquiv_spRootSL2_coe]
  conv_rhs => rw [← Subgroup.map_map]
  exact (Subgroup.mem_map_iff_mem (adjointGroup .E7 K).subtype_injective).symm

end CFSG.SeitzReduction.E7Pilot
