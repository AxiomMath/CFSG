module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13b0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13c_lam_mem_L (h : Q13Om t L S x₁ x₂ lam rho tau om) : lam ∈ L := by
  exact (S4A.generators_mem_L h.c11.toCtx0).2.2

theorem q13c_lam_ne_one (h : Q13Om t L S x₁ x₂ lam rho tau om) : lam ≠ 1 := by
  intro h1
  have h2 : orderOf lam = 1 := h1 ▸ orderOf_one
  rw [h.c11.wreath.ord_lam] at h2
  norm_num at h2

theorem q13c_lam_not_mem_O (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam ∉ ctxO t tau x₁ x₂ := by
  intro hlamO
  have hzle : zpowers lam ≤ ctxO t tau x₁ x₂ := Subgroup.zpowers_le.2 hlamO
  have hU : ctxU t tau x₁ x₂ lam = ctxO t tau x₁ x₂ := by
    rw [ctxU, sup_eq_left.2 hzle]
  have hcard := q13b_card_U h
  rw [hU, h.c11.card_O] at hcard
  norm_num at hcard

theorem q13c_zpowers_lam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ x ∈ zpowers lam, x = 1 ∨ x = lam := by
  intro x hx
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : (orderOf lam : ℤ) = 2 := by
    rw [h.c11.wreath.ord_lam]; norm_num
  have hkm : lam ^ (k % 2) = x := by
    have hh := zpow_mod_orderOf lam k
    rw [h2] at hh
    exact hh.trans hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hkm
    exact hkm.symm
  · right
    rw [h1, zpow_one] at hkm
    exact hkm.symm

theorem q13c_tlam_sq (h : Q13Om t L S x₁ x₂ lam rho tau om) : (t * lam) * (t * lam) = 1 := by
  have ht := q13a_t_mul_self h
  have hl := q13a_lam_mul_self h
  have hcomm := (q13a_t_comm h).1
  calc (t * lam) * (t * lam) = t * (lam * t) * lam := by group
    _ = t * (t * lam) * lam := by rw [hcomm]
    _ = (t * t) * (lam * lam) := by group
    _ = 1 := by rw [ht, hl, mul_one]

theorem q13c_tlam_ne_one (h : Q13Om t L S x₁ x₂ lam rho tau om) : t * lam ≠ 1 := by
  intro h1
  have hlam : lam = t := by
    have h2 : lam = t⁻¹ := by
      calc lam = t⁻¹ * (t * lam) := by group
        _ = t⁻¹ * 1 := by rw [h1]
        _ = t⁻¹ := mul_one _
    rw [h2, inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)]
  exact q13c_lam_not_mem_O h (hlam.symm ▸ q13b_t_mem_O h)

theorem q13c_lam_y (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  calc lam * x₁ ^ 2 * lam⁻¹ = (lam * x₁ * lam⁻¹) ^ 2 :=
        (conj_pow (a := lam) (b := x₁) (i := 2)).symm
    _ = x₂ ^ 2 := by rw [h.c11.wreath.conj_x₁]
    _ = x₁ ^ 2 * (x₁ * x₂) ^ 2 := h.c11.wreath.x₂_sq

theorem q13c_lam_z (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * lam := by
  have hlaminv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (q13a_lam_mul_self h)
  have hconj_x2 : lam * x₂ * lam⁻¹ = x₁ := by
    calc lam * x₂ * lam⁻¹ = lam * (lam * x₁ * lam⁻¹) * lam⁻¹ := by
          rw [h.c11.wreath.conj_x₁]
      _ = (lam * lam) * x₁ * (lam⁻¹ * lam⁻¹) := by group
      _ = 1 * x₁ * 1 := by
            rw [q13a_lam_mul_self h, hlaminv, q13a_lam_mul_self h]
      _ = x₁ := by group
  have hconj : lam * (x₁ * x₂) * lam⁻¹ = x₁ * x₂ := by
    calc lam * (x₁ * x₂) * lam⁻¹ = (lam * x₁ * lam⁻¹) * (lam * x₂ * lam⁻¹) := by group
      _ = x₂ * x₁ := by rw [h.c11.wreath.conj_x₁, hconj_x2]
      _ = x₁ * x₂ := h.c11.wreath.comm.symm
  have hsq : lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (x₁ * x₂) ^ 2 := by
    calc lam * (x₁ * x₂) ^ 2 * lam⁻¹ = (lam * (x₁ * x₂) * lam⁻¹) ^ 2 :=
          (conj_pow (a := lam) (b := x₁ * x₂) (i := 2)).symm
      _ = (x₁ * x₂) ^ 2 := by rw [hconj]
  calc lam * (x₁ * x₂) ^ 2 = lam * (x₁ * x₂) ^ 2 * lam⁻¹ * lam := by group
    _ = (x₁ * x₂) ^ 2 * lam := by rw [hsq]

theorem q13c_lam_not_cent_y (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * x₁ ^ 2 ≠ x₁ ^ 2 * lam := by
  intro hc
  have hy : lam * x₁ ^ 2 * lam⁻¹ = x₁ ^ 2 := by
    calc lam * x₁ ^ 2 * lam⁻¹ = (lam * x₁ ^ 2) * lam⁻¹ := by group
      _ = (x₁ ^ 2 * lam) * lam⁻¹ := by rw [hc]
      _ = x₁ ^ 2 := by group
  have hyz := q13c_lam_y h
  rw [hy] at hyz
  have hz : (x₁ * x₂) ^ 2 = 1 := by
    have h' := congrArg (fun w => (x₁ ^ 2)⁻¹ * w) hyz
    simpa [mul_assoc] using h'.symm
  exact (q13b_z_facts h).1 hz

theorem q13c_lam_cent_tau (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam * tau = tau * lam := by
  exact h.c11.tau_lam.symm

theorem q13c_t_cent_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ n ∈ ctxN tau x₁ x₂, t * n = n * t := by
  intro n hn
  exact q13a_X_comm h t (Subgroup.subset_closure (by simp)) n
    ((p0_V_le_N_le_X t tau x₁ x₂).2 hn)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
