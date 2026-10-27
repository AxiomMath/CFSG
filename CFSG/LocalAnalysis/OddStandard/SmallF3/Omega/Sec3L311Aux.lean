module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Layer
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_of_le {A B K : Subgroup G} (hBA : B ≤ A)
    (h : (K.subgroupOf A).IsSubnormal) : (K.subgroupOf B).IsSubnormal := by
  have h1 := h.comap (Subgroup.inclusion hBA)
  convert h1 using 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
  rfl

theorem Sl23PocketIn.of_le {A B : Subgroup G} {y : G} {K : Subgroup G}
    (h : Sl23PocketIn A y K) (hKB : K ≤ B) (hBA : B ≤ A) : Sl23PocketIn B y K := by
  refine ⟨h.1, le_inf hKB (h.2.1.trans inf_le_right), ?_, h.2.2.2⟩
  exact isSubnormal_subgroupOf_of_le (inf_le_inf hBA le_rfl) h.2.2.1

theorem pocketCore2_le (Y : Subgroup G) (z : G) : pocketCore2 Y z ≤ Y :=
  iSup₂_le fun _ hK => (inSubgroup_le _ _).trans (hK.2.1.trans inf_le_left)

theorem exists_isI4PlusIn_of_pocketExists [Finite G] (hPE : Asc82PocketExists) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) : ∃ z : G, IsI4PlusIn L z := by
  obtain ⟨z, K, hz2, hKL, hK⟩ := hPE G t L hS.involution hS.component (Or.inl hS.inF)
  exact ⟨z, hz2, K, Sl23PocketIn.of_le hK hKL hS.component.le⟩

end CFSG.OddStandard.SmallF3.Omega
