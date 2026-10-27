module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem mem_planeV_of_inv_centralizes (hS : PlaneSetup z K α)
    (hcent : ∀ s ∈ normalizer (Sec5B517Q8 hS.quad : Set H), s * s ∈ Sec5B517Q8 hS.quad →
      (∀ q ∈ Sec5B517Q8 hS.quad, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hS.quad)
    {y : X} (hy : y ∈ normalizer (planeV hS.quad α : Set X)) (hy2 : y * y = 1)
    (hyc : y ∈ centralizer (planeV hS.quad α : Set X)) : y ∈ planeV hS.quad α := by
  obtain ⟨s, rfl⟩ := hS.surj y
  have hsN : s ∈ normalizer (Sec5B517Q8 hS.quad : Set H) :=
    (mem_normalizer_planeV_iff hS).mp hy
  have hs2 : s * s ∈ Sec5B517Q8 hS.quad := by
    have hker : s * s ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, hy2]
    exact ker_le_Q8 hS hker
  refine (mem_planeV_iff hS).mpr (hcent s hsN hs2 ?_)
  intro q hq
  rw [← hS.ker, MonoidHom.mem_ker]
  have hcomm : α q * α s = α s * α q :=
    (Subgroup.mem_centralizer_iff.mp hyc) (α q) ((mem_planeV_iff hS).mpr hq)
  rw [show α (s * q * s⁻¹ * q⁻¹) = α s * α q * (α s)⁻¹ * (α q)⁻¹ by
    simp only [map_mul, map_inv]]
  rw [← hcomm]
  group

end CFSG.OddStandard.SmallF3.Omega
