module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbDefs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Subgroup

variable {G : Type} [Group G]

theorem charIn_commutator3 (U : Subgroup G) : CharIn (⁅⁅U, U⁆, U⁆ : Subgroup G) U := by
  refine ⟨Subgroup.commutator_le_of_le (Subgroup.commutator_le_of_le le_rfl le_rfl) le_rfl, ?_⟩
  have hTop : (⊤ : Subgroup ↥U).map U.subtype = U := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have heq : (⁅⁅U, U⁆, U⁆ : Subgroup G) = Subgroup.map U.subtype
      ⁅⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆, (⊤ : Subgroup ↥U)⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hTop]
  rw [heq]
  have : (Subgroup.map U.subtype
      ⁅⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆, (⊤ : Subgroup ↥U)⁆).subgroupOf U =
      ⁅⁅(⊤ : Subgroup ↥U), (⊤ : Subgroup ↥U)⁆, (⊤ : Subgroup ↥U)⁆ :=
    Subgroup.comap_map_eq_self_of_injective U.subtype_injective _
  rw [this]
  infer_instance

theorem charIn_inf_centralizer {W T : Subgroup G} (hW : CharIn W T) :
    CharIn (T ⊓ Subgroup.centralizer (W : Set G)) T := by
  refine ⟨inf_le_left, ?_⟩
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (t : G) ∈ T ⊓ Subgroup.centralizer (W : Set G) := Subgroup.mem_subgroupOf.mp ht
  show φ t ∈ (T ⊓ Subgroup.centralizer (W : Set G)).subgroupOf T
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(φ t).2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hw' : φ.symm ⟨w, hW.1 hw⟩ ∈ W.subgroupOf T :=
    Subgroup.characteristic_iff_map_le.mp hW.2 φ.symm
      ⟨⟨w, hW.1 hw⟩, Subgroup.mem_subgroupOf.mpr hw, rfl⟩
  have hc := Subgroup.mem_centralizer_iff.mp ht'.2 _ (Subgroup.mem_subgroupOf.mp hw')
  have hc' : φ.symm ⟨w, hW.1 hw⟩ * t = t * φ.symm ⟨w, hW.1 hw⟩ := Subtype.ext hc
  have h2 := congrArg φ hc'
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  exact congrArg Subtype.val h2

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
