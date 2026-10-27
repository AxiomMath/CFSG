module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_isI4PlusIn_top_of_subtype {I : Subgroup G} {y : G} (hyI : y ∈ I)
    (h : IsI4PlusIn I y) : IsI4PlusIn (⊤ : Subgroup ↥I) ⟨y, hyI⟩ := by
  rw [IsI4PlusIn] at h ⊢
  obtain ⟨hy2, K, hK⟩ := h
  refine ⟨(Subgroup.orderOf_mk y hyI).trans hy2, ?_⟩
  have hKI : K ≤ I := hK.2.1.trans inf_le_left
  let K' : Subgroup ↥I := K.subgroupOf I
  let M : Subgroup ↥I := ⊤ ⊓ Subgroup.centralizer ({⟨y, hyI⟩} : Set ↥I)
  let M₀ : Subgroup G := I ⊓ Subgroup.centralizer ({y} : Set G)
  refine ⟨K', ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact hK.1
  · refine le_inf le_top ?_
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hK.2.1 (Subgroup.mem_subgroupOf.mp hk)).2
  · show (K'.subgroupOf M).IsSubnormal
    let ι : ↥M →* ↥M₀ :=
      { toFun := fun m => ⟨(m : ↥I).1,
          ⟨(m : ↥I).2, Subgroup.mem_centralizer_singleton_iff.mpr
            (congrArg Subtype.val
              (Subgroup.mem_centralizer_singleton_iff.mp m.2.2))⟩⟩
        map_one' := by ext; rfl
        map_mul' := by intro a b; ext; rfl }
    have hcomap : (K.subgroupOf M₀).comap ι = K'.subgroupOf M := by
      ext m
      exact Iff.rfl
    have hsub' : ((K.subgroupOf M₀).comap ι).IsSubnormal :=
      Subgroup.IsSubnormal.comap ι hK.2.2.1
    rw [← hcomap]
    exact hsub'
  · exact isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKI).symm hK.2.2.2

end CFSG.OddStandard.SmallF3.Omega
