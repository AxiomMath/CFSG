module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXPlaneComponentOrbitRank

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_conj_mem' {Y : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate Y g ↔ g * x * g⁻¹ ∈ Y := by
  rw [CFSG.conjugate, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]

@[simp] theorem cfsgConjugate_one (Y : Subgroup G) : CFSG.conjugate Y 1 = Y := by
  ext x
  rw [mem_conjugate_iff_conj_mem']
  simp

theorem conjugate_eq_self_iff {Y : Subgroup G} {g : G} :
    CFSG.conjugate Y g = Y ↔ g ∈ normalizer (Y : Set G) := by
  rw [CFSG.conjugate, map_conj_eq_self_iff]
  exact ⟨fun h => by simpa using Subgroup.inv_mem _ h, fun h => Subgroup.inv_mem _ h⟩

end CFSG.LocalAnalysis.GorensteinLyons
