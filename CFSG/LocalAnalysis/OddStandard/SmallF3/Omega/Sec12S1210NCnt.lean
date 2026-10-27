module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JG

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec12N_index_dvd {N W Θ : Type*} [Group N] [Finite N] [Group W] [Group Θ]
    (φ : N →* W) (hφ : Function.Surjective φ) (β : N →* Θ) {B2 H : Subgroup W} (hBH : B2 ≤ H)
    (hker : ∀ n, β n = 1 ↔ φ n ∈ B2) {t : N}
    (hcomm : ∀ w ∈ H, w * φ t * w⁻¹ * (φ t)⁻¹ ∈ B2) :
    Nat.card H ∣ Nat.card B2 * Nat.card (Subgroup.centralizer ({β t} : Set Θ)) := by
  set P1 : Subgroup N := H.comap φ with hP1
  have hle : P1.map β ≤ Subgroup.centralizer ({β t} : Set Θ) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 : β (n * t * n⁻¹ * t⁻¹) = 1 := by
      rw [hker]
      have := hcomm (φ n) (Subgroup.mem_comap.mp hn)
      simpa only [map_mul, map_inv] using this
    have h2 : β n * β t * (β n)⁻¹ * (β t)⁻¹ = 1 := by
      simpa only [map_mul, map_inv] using h1
    rw [mul_inv_eq_one] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hkerφ_le : φ.ker ≤ P1 := fun n hn => by
    show φ n ∈ H
    rw [MonoidHom.mem_ker.mp hn]
    exact H.one_mem
  have hcardP1 : Nat.card φ.ker * Nat.card H = Nat.card P1 := by
    have h := sec12J_card_inf_ker_mul φ P1
    rwa [inf_eq_right.mpr hkerφ_le, Subgroup.map_comap_eq_self_of_surjective hφ] at h
  have hkerβ : β.ker = B2.comap φ := by
    ext n
    rw [MonoidHom.mem_ker, hker]
    rfl
  have hkerφ_le' : φ.ker ≤ B2.comap φ := fun n hn => by
    show φ n ∈ B2
    rw [MonoidHom.mem_ker.mp hn]
    exact B2.one_mem
  have hcardKβ : Nat.card φ.ker * Nat.card B2 = Nat.card β.ker := by
    have h := sec12J_card_inf_ker_mul φ (B2.comap φ)
    rw [hkerβ]
    rwa [inf_eq_right.mpr hkerφ_le', Subgroup.map_comap_eq_self_of_surjective hφ] at h
  have hkerβ_le : β.ker ≤ P1 := by
    rw [hkerβ]
    exact Subgroup.comap_mono hBH
  have hcardP1' : Nat.card β.ker * Nat.card (P1.map β) = Nat.card P1 := by
    have h := sec12J_card_inf_ker_mul β P1
    rwa [inf_eq_right.mpr hkerβ_le] at h
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hHeq : Nat.card H = Nat.card B2 * Nat.card (P1.map β) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hcardP1, ← hcardP1', ← hcardKβ, mul_assoc]
  rw [hHeq]
  exact mul_dvd_mul_left _ (Subgroup.card_dvd_of_le hle)

end CFSG.OddStandard.SmallF3.Omega
