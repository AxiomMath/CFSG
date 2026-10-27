module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GS7
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GDC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GLB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GDS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GW

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_level3 [Finite G] (hKB : Asc82FactPocketLift) (hLB : AschLBalance G)
    (hA2 : AschA2 G) (hA : L34GLemmaA G) {v v₂ u₂ w : G} {D₂ K₂ : Subgroup G}
    (hdat : Sec3PocketData v₂ D₂ u₂ K₂) (hv : orderOf v = 2) (hvv₂ : v * v₂ = v₂ * v)
    (hne : CFSG.conjugate D₂ v ≠ D₂) (hww : w * w = v₂) (hwu : w * u₂ = u₂ * w)
    (hLw : ∀ l ∈ CFSG.conjugate D₂ v, w * l = l * w) : False := by
  have hDI4 : IsI4PlusIn D₂ u₂ := ⟨hdat.involution_y, K₂, l34g_sl23PocketIn_of_data hdat⟩
  obtain ⟨I₂, hI₂, hI₂F, hle⟩ := l34g_lbal_step hLB hA2 hdat.involution_x hv
    hdat.involution_y hvv₂ hdat.component hdat.inFStar hdat.mem hne
  have hvC : v ∈ centralizer ({v₂} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hvv₂
  have hwN : w ∈ normalizer ((centralizer ({u₂} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hwu)
  have hfix : CFSG.conjugate I₂ v₂ = I₂ :=
    l34g_conj_fixed_of_sqrt hdat.involution_x hww hwN hI₂
      (hdat.component.conjugate hvC).isQuasisimple hLw hle
  refine l34g_direct_closure hKB hA hv hdat.involution_x hvv₂ hdat.component hdat.inFStar
    hdat.mem hDI4 hI₂ hI₂F hfix ?_
  rw [hfix, sup_idem] at hle
  exact hle

theorem l34g_levels23 [Finite G] (hKB : Asc82FactPocketLift) (hLB : AschLBalance G)
    (hA2 : AschA2 G) (hP : L34GPocketComm G) (hA : L34GLemmaA G) {v x u₁ : G}
    {D K₁ : Subgroup G} (hdat : Sec3PocketData v D u₁ K₁) (hx : orderOf x = 2)
    (hxv : x * v = v * x) (hne : CFSG.conjugate D x ≠ D) : False := by
  have hv : orderOf v = 2 := hdat.involution_x
  have hu₁D : u₁ ∈ D := hdat.mem
  have hu4 : IsI4PlusIn D u₁ := ⟨hdat.involution_y, K₁, l34g_sl23PocketIn_of_data hdat⟩
  obtain ⟨I₁, hI₁, hI₁F, hle₁⟩ := l34g_lbal_step hLB hA2 hv hx hdat.involution_y hxv
    hdat.component hdat.inFStar hu₁D hne
  by_cases hIv : CFSG.conjugate I₁ v = I₁
  ·
    refine l34g_direct_closure hKB hA hx hv hxv hdat.component hdat.inFStar hu₁D hu4 hI₁ hI₁F
      hIv ?_
    rw [hIv, sup_idem] at hle₁
    exact hle₁
  ·
    obtain ⟨u₂, K₂, hdat₂, hne₂⟩ := l34g_diag_step hv hx hxv hdat.component hu₁D hu4 hI₁ hI₁F
      hle₁ hIv
    have hvu₁ : v * u₁ = u₁ * v :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hdat.component.1 hu₁D)).symm
    have hvx : Commute v x := hxv.symm
    have hvv₂ : v * (x⁻¹ * u₁ * x) = (x⁻¹ * u₁ * x) * v :=
      ((hvx.inv_right.mul_right (show Commute v u₁ from hvu₁)).mul_right hvx)
    obtain ⟨w, hww, hw₁, hw₂⟩ := l34g_w_exists hP (x := x) hdat hI₁ hI₁F
    refine l34g_level3 hKB hLB hA2 hA hdat₂ hv hvv₂ hne₂ hww (hw₁ u₂ hdat₂.mem) ?_
    intro l hl
    refine hw₂ l ?_
    rwa [l34g_conjugate_conjugate, hxv, ← l34g_conjugate_conjugate] at hl

end CFSG.OddStandard.SmallF3.Omega
