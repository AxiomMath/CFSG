module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem fg_isI4PlusIn_iff_of_cover {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    {L : Subgroup G} {φ : ↥L →* P} (h : OddCentralCover φ) {w : G} (hw : w ∈ L)
    (hw2 : orderOf w = 2) :
    IsI4PlusIn L w ↔ IsI4PlusIn (⊤ : Subgroup P) (φ ⟨w, hw⟩) := by
  classical
  constructor
  · intro hwI
    have htop : IsI4PlusIn (⊤ : Subgroup ↥L) (⟨w, hw⟩ : ↥L) := by
      have h' := l34g_x_isI4PlusIn_subgroupOf (H := L) (V := L) (y := w) (le_refl L) hw hwI
      rwa [Subgroup.subgroupOf_self] at h'
    have hmap := l34g_x_isI4PlusIn_map h (V := ⊤) htop
    rwa [Subgroup.map_top_of_surjective φ h.surjective] at hmap
  · intro hP
    have hww : w * w = 1 := by
      rw [← pow_two]
      exact hw2 ▸ pow_orderOf_eq_one w
    have haa : (⟨w, hw⟩ : ↥L) * ⟨w, hw⟩ = 1 := Subtype.ext hww
    have htop : IsI4PlusIn (⊤ : Subgroup ↥L) (⟨w, hw⟩ : ↥L) :=
      l34g_x_isI4PlusIn_top_of_cover (A := ↥L) (P := P) h haa hP
    have htop' : IsI4PlusIn (⊤ : Subgroup ↥(⊤ : Subgroup ↥L))
        (⟨⟨w, hw⟩, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup ↥L)) := by
      have h' := l34g_x_isI4PlusIn_subgroupOf (H := (⊤ : Subgroup ↥L))
        (V := (⊤ : Subgroup ↥L)) (y := (⟨w, hw⟩ : ↥L)) (le_refl _) (Subgroup.mem_top _) htop
      rwa [Subgroup.subgroupOf_self] at h'
    have hmap := l34g_x_isI4PlusIn_map_inj (X := ↥L) L.subtype L.subtype_injective
      (J₀ := (⊤ : Subgroup ↥L)) (Subgroup.mem_top _) htop'
    rwa [Subgroup.map_top, Subgroup.range_subtype] at hmap

end CFSG.OddStandard.SmallF3.Omega
