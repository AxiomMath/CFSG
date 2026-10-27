module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCov
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTFix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXSet

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_x_isComponentIn_map [Finite G] {H : Subgroup G} (hH : InFStar H) {a : G}
    (ha : a * a = 1) (haN : a ∈ normalizer (H : Set G)) {α : MulAut (↥H ⧸ oddCore ↥H)}
    (hα : ∀ x : ↥H, (QuotientGroup.mk (conjAut H ha haN x) : ↥H ⧸ oddCore ↥H) =
      α (QuotientGroup.mk x))
    {J : Subgroup G} (hJ : IsComponentIn J (H ⊓ centralizer ({a} : Set G))) :
    IsComponentIn ((J.subgroupOf H).map (QuotientGroup.mk' (oddCore ↥H))) (L34GFix α) := by
  have hJH : J ≤ H := hJ.1.trans inf_le_left
  have h1 : IsComponentIn (J.subgroupOf H) (fixSub (conjAut H ha haN)) := by
    rw [← sec63PT_isComponentIn_map_iff H.subtype H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hJH,
      sec63PT_map_subtype_fixSub H ha haN]
    exact hJ
  have h2 := sec63PT_isComponentIn_map (QuotientGroup.mk' (oddCore ↥H))
    (l34g_x_cover hH).ker_le_center h1
  rwa [sec63PT_map_fixSub (l34g_x_cover hH) (conjAut_mul_self H ha haN) hα,
    ← l34g_fix_eq_fixSub] at h2

theorem l34g_x_isComponentIn_lift [Finite G] {H : Subgroup G} (hH : InFStar H) {a : G}
    (ha : a * a = 1) (haN : a ∈ normalizer (H : Set G)) {α : MulAut (↥H ⧸ oddCore ↥H)}
    (hα : ∀ x : ↥H, (QuotientGroup.mk (conjAut H ha haN x) : ↥H ⧸ oddCore ↥H) =
      α (QuotientGroup.mk x))
    {Jb : Subgroup (↥H ⧸ oddCore ↥H)} (hJb : IsComponentIn Jb (L34GFix α)) :
    IsComponentIn ((coverDerived (QuotientGroup.mk' (oddCore ↥H)) Jb).map H.subtype)
      (H ⊓ centralizer ({a} : Set G)) := by
  rw [l34g_fix_eq_fixSub] at hJb
  have h2 := l34g_x_isComponentIn_coverDerived_fix (l34g_x_cover hH)
    (σ := conjAut H ha haN) hα hJb
  have h3 := (sec63PT_isComponentIn_map_iff H.subtype H.subtype_injective).mpr h2
  rwa [sec63PT_map_subtype_fixSub H ha haN] at h3

end CFSG.OddStandard.SmallF3.Omega
