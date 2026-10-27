module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH0

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H}

private lemma K_le_all (K : Fin 4 → Subgroup H) (i : Fin 4) : K i ≤ Sec5B517All K := by
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem planeRho_mem (hq : Sec5B517Quad K z) (α : H →* X) (i : Fin 4) :
    planeRho hq α i ∈ normalizer (planeV hq α : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [planeV, Subgroup.mem_map] at hh ⊢
    obtain ⟨q, hqQ, rfl⟩ := hh
    refine ⟨elt3 hq i * q * (elt3 hq i)⁻¹, ?_, ?_⟩
    · exact Sec5B517Q8.conj_mem hq (K_le_all K i (elt3_mem hq i)) hqQ
    · simp only [map_mul, map_inv, planeRho]
  · intro hh
    rw [planeV, Subgroup.mem_map] at hh ⊢
    obtain ⟨q, hqQ, hqeq⟩ := hh
    refine ⟨(elt3 hq i)⁻¹ * q * elt3 hq i, ?_, ?_⟩
    · simpa only [inv_inv] using Sec5B517Q8.conj_mem hq
        (K_le_all K i ((K i).inv_mem (elt3_mem hq i))) hqQ
    · simp only [map_mul, map_inv, planeRho] at hqeq ⊢
      rw [hqeq]
      group

theorem planeRho_order {α : H →* X} (hS : PlaneSetup z K α) (i : Fin 4) :
    orderOf (planeRho hS.quad α i) = 3 := by
  have hr3 : (elt3 hS.quad i) ^ 3 = 1 := by
    rw [← elt3_order hS.quad i]
    exact pow_orderOf_eq_one _
  have h3 : (planeRho hS.quad α i) ^ 3 = 1 := by
    simp only [planeRho]
    rw [← map_pow, hr3, map_one]
  refine orderOf_eq_prime (p := 3) h3 ?_
  intro h
  rw [planeRho] at h
  have hrker : elt3 hS.quad i ∈ α.ker := MonoidHom.mem_ker.mpr h
  have hrz : elt3 hS.quad i ∈ zpowers z := by
    rw [← hS.ker]
    exact hrker
  have hzord : orderOf z = 2 :=
    orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hS.quad.z_sq) hS.quad.z_ne
  have hdvd : orderOf (elt3 hS.quad i) ∣ orderOf z := orderOf_dvd_of_mem_zpowers hrz
  rw [hzord, elt3_order hS.quad i] at hdvd
  norm_num at hdvd

theorem planeRho_comm (hq : Sec5B517Quad K z) (α : H →* X) (i j : Fin 4) :
    planeRho hq α i * planeRho hq α j = planeRho hq α j * planeRho hq α i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · have h := hq.comm i j hij (elt3 hq i) (elt3_mem hq i) (elt3 hq j) (elt3_mem hq j)
    simp only [planeRho]
    rw [← map_mul, ← map_mul, h]

theorem planeRho_inv (hq : Sec5B517Quad K z) (α : H →* X) (i : Fin 4) :
    ∀ w ∈ planeW hq α i, planeRho hq α i * w * (planeRho hq α i)⁻¹ ∈ planeW hq α i := by
  intro w hw
  rw [planeW, Subgroup.mem_map] at hw ⊢
  obtain ⟨u, ⟨huQ, huK⟩, rfl⟩ := hw
  refine ⟨elt3 hq i * u * (elt3 hq i)⁻¹, ⟨?_, ?_⟩, ?_⟩
  · exact Sec5B517Q8.conj_mem hq (K_le_all K i (elt3_mem hq i)) huQ
  · exact (K i).mul_mem ((K i).mul_mem (elt3_mem hq i) huK)
      ((K i).inv_mem (elt3_mem hq i))
  · simp only [map_mul, map_inv, planeRho]

theorem planeRho_triv (hq : Sec5B517Quad K z) (α : H →* X) (i j : Fin 4) (hij : i ≠ j) :
    ∀ w ∈ planeW hq α j, planeRho hq α i * w = w * planeRho hq α i := by
  intro w hw
  rw [planeW, Subgroup.mem_map] at hw
  obtain ⟨u, ⟨huQ, huK⟩, rfl⟩ := hw
  have h := hq.comm i j hij (elt3 hq i) (elt3_mem hq i) u huK
  simp only [planeRho]
  rw [← map_mul, ← map_mul, h]

end CFSG.OddStandard.SmallF3.Omega
