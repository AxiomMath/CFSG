module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E7b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem isSylow2Of_top_of_setup [Finite H] (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j)
    (hcent : ∀ s ∈ normalizer (Sec5B517Q8 hS.quad : Set H), s * s ∈ Sec5B517Q8 hS.quad →
      (∀ q ∈ Sec5B517Q8 hS.quad, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hS.quad)
    (hpar : ∀ w ∈ normalizer (Sec5B517Q8 hS.quad : Set H),
      (∀ i, CFSG.conjugate (K i) w = K i) →
      (∀ q ∈ Sec5B517Q8 hS.quad, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ Sec5B517Q8 hS.quad ⊓ K i,
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}))
    {T : Subgroup H} (hQT : Sec5B517Q8 hS.quad ≤ T)
    (hT : IsSylow2Of T (normalizer (Sec5B517Q8 hS.quad : Set H))) :
    IsSylow2Of T (⊤ : Subgroup H) := by
  classical
  haveI : Finite X := Finite.of_surjective α hS.surj
  have hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α) :=
    planeSys_of_setup hS hperm
  have hparX : PlaneParity (planeV hS.quad α) (planeW hS.quad α) :=
    planeParity_of_setup hS hperm hpar
  have hCX : ∀ y ∈ normalizer (planeV hS.quad α : Set X), y * y = 1 →
      y ∈ centralizer (planeV hS.quad α : Set X) → y ∈ planeV hS.quad α :=
    fun y hy hy2 hyc => mem_planeV_of_inv_centralizes hS hcent hy hy2 hyc
  have hker : α.ker ≤ T := (ker_le_Q8 hS).trans hQT
  have hNmap : (normalizer (Sec5B517Q8 hS.quad : Set H)).map α ≤
      normalizer (planeV hS.quad α : Set X) := by
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_normalizer_planeV_iff hS).mpr hn
  have hNmap_eq : (normalizer (Sec5B517Q8 hS.quad : Set H)).map α =
      normalizer (planeV hS.quad α : Set X) := by
    refine le_antisymm hNmap ?_
    intro y hy
    obtain ⟨x, rfl⟩ := hS.surj y
    exact Subgroup.mem_map.mpr ⟨x, (mem_normalizer_planeV_iff hS).mp hy, rfl⟩
  have hTmap_le : T.map α ≤ normalizer (planeV hS.quad α : Set X) :=
    (Subgroup.map_mono hT.1).trans hNmap
  have hTmap_sylow : IsSylow2Of (T.map α) (normalizer (planeV hS.quad α : Set X)) := by
    refine ⟨hTmap_le, hT.2.1.map α, ?_⟩
    rw [← hNmap_eq, relIndex_map_eq_of_ker_le α hker hT.1]
    exact hT.2.2
  have hVT : planeV hS.quad α ≤ T.map α := Subgroup.map_mono hQT
  have hSylowX : IsSylow2Of (T.map α) (⊤ : Subgroup X) :=
    isSylow2Of_top hSys hparX hCX hVT hTmap_sylow
  refine ⟨le_top, hT.2.1, ?_⟩
  have hrel : (T.map α).relIndex (⊤ : Subgroup X) = T.relIndex (⊤ : Subgroup H) := by
    have h := relIndex_map_eq_of_ker_le α hker (le_top : T ≤ ⊤)
    rwa [Subgroup.map_top_of_surjective α hS.surj] at h
  rw [← hrel]
  exact hSylowX.2.2

end CFSG.OddStandard.SmallF3.Omega
