module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH1

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H}

private lemma s888ph3b_mem_zpowers_involution {u x : H} (hu : u * u = 1)
    (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hu2 : u ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hu
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, hu2, one_zpow]
  · right
    rw [hm, zpow_add_one, zpow_mul, hu2, one_zpow, one_mul]

private lemma s888ph3b_iso_z_eq_neg_one (hq : Sec5B517Quad K z) {i : Fin 4}
    (e : ↥(K i) ≃* SL23) : e ⟨z, hq.z_mem i⟩ = -1 := by
  have hsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul]
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) * ⟨z, hq.z_mem i⟩ = 1 :=
      Subtype.ext (by simpa using hq.z_sq)
    rw [hsub, map_one]
  rcases sl23_unique_involution _ hsq with h1 | hneg
  · exfalso
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h1, map_one])
    exact hq.z_ne (congrArg Subtype.val hsub)
  · exact hneg

private lemma s888ph3b_sl23_order_three_fpf :
    ∀ ρ ν : SL23, ρ ^ 3 = 1 → ρ ≠ 1 → ν ^ 4 = 1 → ν ≠ 1 → ν ≠ -1 →
      ρ * ν * ρ⁻¹ * ν⁻¹ ≠ 1 ∧ ρ * ν * ρ⁻¹ * ν⁻¹ ≠ -1 := by
  decide +kernel

theorem planeRho_fpf (hq : Sec5B517Quad K z) (α : H →* X) (hker : α.ker = zpowers z)
    (i : Fin 4) :
    ∀ w ∈ planeW hq α i, w ≠ 1 → planeRho hq α i * w * (planeRho hq α i)⁻¹ ≠ w := by
  intro w hw hw1 hfix
  rw [planeW, Subgroup.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  have huKi : u ∈ K i := hu.2
  have hu4 : u ^ 4 = 1 := ((mem_inf_K_iff hq i).mp hu).2
  let r := elt3 hq i
  have hrKi : r ∈ K i := elt3_mem hq i
  have hord : orderOf r = 3 := elt3_order hq i
  have hr3 : r ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hord])
  have hr1 : r ≠ 1 := by
    intro h
    have h1 := hord
    rw [h] at h1
    simp at h1
  have hfix' : α r * α u * (α r)⁻¹ = α u := hfix
  have hαc : α (r * u * r⁻¹ * u⁻¹) = 1 := by
    have h : α r * α u * (α r)⁻¹ * (α u)⁻¹ = 1 := by
      rw [hfix', mul_inv_cancel]
    simpa only [map_mul, map_inv] using h
  have hcmem : r * u * r⁻¹ * u⁻¹ ∈ K i :=
    (K i).mul_mem ((K i).mul_mem ((K i).mul_mem hrKi huKi) ((K i).inv_mem hrKi))
      ((K i).inv_mem huKi)
  have hc_ker : r * u * r⁻¹ * u⁻¹ ∈ zpowers z := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hαc
  obtain ⟨e⟩ := hq.iso i
  have hze : e ⟨z, hq.z_mem i⟩ = -1 := s888ph3b_iso_z_eq_neg_one hq e
  have hsubr : (⟨r, hrKi⟩ : ↥(K i)) ^ 3 = 1 := Subtype.ext (by simpa using hr3)
  have hsubu : (⟨u, huKi⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hu4)
  have hρ3 : (e ⟨r, hrKi⟩) ^ 3 = 1 := by rw [← map_pow, hsubr, map_one]
  have hρ1 : e ⟨r, hrKi⟩ ≠ 1 := by
    intro h
    have hsub : (⟨r, hrKi⟩ : ↥(K i)) = 1 := e.injective (by rw [h, map_one])
    exact hr1 (congrArg Subtype.val hsub)
  have hν4 : (e ⟨u, huKi⟩) ^ 4 = 1 := by rw [← map_pow, hsubu, map_one]
  have hν1 : e ⟨u, huKi⟩ ≠ 1 := by
    intro h
    have hsub : (⟨u, huKi⟩ : ↥(K i)) = 1 := e.injective (by rw [h, map_one])
    have hu1 : u = 1 := congrArg Subtype.val hsub
    exact hw1 (by rw [hu1, map_one])
  have hαz : α z = 1 := by
    have : z ∈ α.ker := by rw [hker]; exact Subgroup.mem_zpowers z
    exact MonoidHom.mem_ker.mp this
  have hνm1 : e ⟨u, huKi⟩ ≠ -1 := by
    intro h
    have hsub : (⟨u, huKi⟩ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := e.injective (by rw [h, ← hze])
    have huz : u = z := congrArg Subtype.val hsub
    exact hw1 (by rw [huz, hαz])
  have hfp := s888ph3b_sl23_order_three_fpf (e ⟨r, hrKi⟩) (e ⟨u, huKi⟩)
    hρ3 hρ1 hν4 hν1 hνm1
  have hc_eq : e ⟨r * u * r⁻¹ * u⁻¹, hcmem⟩ =
      e ⟨r, hrKi⟩ * e ⟨u, huKi⟩ * (e ⟨r, hrKi⟩)⁻¹ * (e ⟨u, huKi⟩)⁻¹ := by
    have hsub : (⟨r * u * r⁻¹ * u⁻¹, hcmem⟩ : ↥(K i)) =
        ⟨r, hrKi⟩ * ⟨u, huKi⟩ * ⟨r, hrKi⟩⁻¹ * ⟨u, huKi⟩⁻¹ := rfl
    rw [hsub]
    simp only [map_mul, map_inv]
  rcases s888ph3b_mem_zpowers_involution hq.z_sq hc_ker with hc | hc
  · apply hfp.1
    rw [← hc_eq]
    have : (⟨r * u * r⁻¹ * u⁻¹, hcmem⟩ : ↥(K i)) = 1 := Subtype.ext (by simpa using hc)
    rw [this, map_one]
  · apply hfp.2
    rw [← hc_eq]
    have : (⟨r * u * r⁻¹ * u⁻¹, hcmem⟩ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := Subtype.ext hc
    rw [this, hze]

end CFSG.OddStandard.SmallF3.Omega
