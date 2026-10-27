module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GA2a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma ga2b_zpowers_two {t : H} (hzsq : z * z = 1) (ht : t ∈ zpowers z) :
    t = 1 ∨ t = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact hzsq
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem h73X_of_setup (hS : PlaneSetup z K α)
    (hSys : PlaneSys (planeV hS.quad α) (planeW hS.quad α))
    (hCd : ∀ d : H, d ∈ Sec5B517Q8 hS.quad → d * d = 1 → d ≠ 1 → d ≠ z →
      (∃ i j : Fin 4, i ≠ j ∧ d ∈ K i ⊔ K j) →
        centralizer ({d} : Set H) ≤ normalizer (Sec5B517Q8 hS.quad : Set H)) :
    ∀ v : planeV hS.quad α, SuppTwo hSys v →
      centralizer ({(v : X)} : Set X) ≤ normalizer (planeV hS.quad α : Set X) := by
  intro v hv y hy
  obtain ⟨d, i, j, hij, hdQ, hd2, hd1, hdz, hdK, hαd, r, hrQ, hrd⟩ :=
    exists_involution_of_suppTwo hS hSys v hv
  obtain ⟨x, rfl⟩ := hS.surj y
  have hcomm : α x * (v : X) = (v : X) * α x := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hconj : α (x * d * x⁻¹) = α d := by
    rw [map_mul, map_mul, map_inv, hαd, hcomm]
    group
  have hker : d⁻¹ * (x * d * x⁻¹) ∈ zpowers z := by
    rw [← hS.ker, MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
  rcases ga2b_zpowers_two hS.quad.z_sq hker with h | h
  · have hxd0 : x * d * x⁻¹ = d := by
      have h' := congrArg (d * ·) h
      simpa using h'
    have hxd : x ∈ centralizer ({d} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * d = (x * d * x⁻¹) * x := by group
        _ = d * x := by rw [hxd0]
    exact (mem_normalizer_planeV_iff hS).mpr
      (hCd d hdQ hd2 hd1 hdz ⟨i, j, hij, hdK⟩ hxd)
  · have hxd' : x * d * x⁻¹ = d * z := by
      have h' := congrArg (d * ·) h
      simpa using h'
    have hrx : r⁻¹ * x ∈ centralizer ({d} : Set H) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : (r⁻¹ * x) * d * (r⁻¹ * x)⁻¹ = d := by
        calc (r⁻¹ * x) * d * (r⁻¹ * x)⁻¹ = r⁻¹ * (x * d * x⁻¹) * r := by group
          _ = r⁻¹ * (d * z) * r := by rw [hxd']
          _ = r⁻¹ * (r * d * r⁻¹) * r := by rw [hrd]
          _ = d := by group
      calc (r⁻¹ * x) * d = ((r⁻¹ * x) * d * (r⁻¹ * x)⁻¹) * (r⁻¹ * x) := by group
        _ = d * (r⁻¹ * x) := by rw [e1]
    have hrxN := hCd d hdQ hd2 hd1 hdz ⟨i, j, hij, hdK⟩ hrx
    have hrN : r ∈ normalizer (Sec5B517Q8 hS.quad : Set H) := Subgroup.le_normalizer hrQ
    have hxN : x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) := by
      have h3 := (normalizer (Sec5B517Q8 hS.quad : Set H)).mul_mem hrN hrxN
      simpa using h3
    exact (mem_normalizer_planeV_iff hS).mpr hxN

end CFSG.OddStandard.SmallF3.Omega
