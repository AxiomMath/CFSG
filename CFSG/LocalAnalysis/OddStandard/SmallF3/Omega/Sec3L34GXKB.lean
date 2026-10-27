module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXCovG
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXPkLift
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem asc82FactPocketLift_of_core (h : Asc82CoreKGB) : Asc82FactPocketLift := by
  intro G _ _ H hH a ha2 haN J hJ b hbJ hbI
  have haa : a * a = 1 := by
    have h1 := pow_orderOf_eq_one a
    rwa [ha2, pow_two] at h1
  have hJH : J ≤ H := hJ.1.trans inf_le_left
  have hbH : b ∈ H := hJH hbJ
  have hbb : b * b = 1 := by
    have h1 := pow_orderOf_eq_one b
    rwa [hbI.1, pow_two] at h1
  obtain ⟨α, hα2, hα⟩ := l34g_x_induced haa haN
  have hJb := l34g_x_isComponentIn_map hH haa haN hα hJ
  have hmem : (QuotientGroup.mk (⟨b, hbH⟩ : ↥H) : ↥H ⧸ oddCore ↥H) ∈
      (J.subgroupOf H).map (QuotientGroup.mk' (oddCore ↥H)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hbJ)
  have hI := l34g_x_isI4PlusIn_map (l34g_x_cover hH)
    (l34g_x_isI4PlusIn_subgroupOf hJH hbH hbI)
  have h3 := h _ (l34g_x_starQuotient hH) α hα2 _ hJb _ hmem hI
  have hbb' : (⟨b, hbH⟩ : ↥H) * ⟨b, hbH⟩ = 1 := Subtype.ext hbb
  exact isI4PlusIn_of_top hbH (l34g_x_isI4PlusIn_top_of_cover (l34g_x_cover hH) hbb' h3)

end CFSG.OddStandard.SmallF3.Omega
