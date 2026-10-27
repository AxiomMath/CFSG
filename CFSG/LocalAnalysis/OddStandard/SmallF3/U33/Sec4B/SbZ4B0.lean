module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbM4Stmt

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Q

theorem t_mul_self (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t * t = 1 := by
  have h1 := pow_orderOf_eq_one t
  rw [hc.hyp.ord_t] at h1
  simpa [pow_two] using h1

theorem t_ne_one (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t ≠ 1 := by
  intro ht
  have h2 : orderOf t = 1 := by rw [ht, orderOf_one]
  rw [hc.hyp.ord_t] at h2
  omega

theorem tau_mul_self (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : tau * tau = 1 := by
  have h := hc.l44.1
  rwa [pow_two] at h

theorem tau_ne_one (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : tau ≠ 1 :=
  fun h => hc.tau_not_mem (h ▸ one_mem _)

theorem t_ne_tau (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t ≠ tau :=
  fun h => hc.tau_not_mem (h ▸ mem_sup_left hc.hyp.mem_twoCore)

theorem t_comm_tau (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t * tau = tau * t := by
  have ht : t ∈ S ⊓ centralizer (S : Set G) := hc.center_ge (subset_closure (by simp))
  exact (mem_centralizer_iff.mp ht.2 tau hc.tau_mem).symm

theorem rho_comm_t (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : rho * t = t * rho := by
  have h : t ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_rho]; exact subset_closure (by simp)
  exact mem_centralizer_iff.mp h.2 rho (Set.mem_singleton rho)

theorem rho_comm_tau (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : rho * tau = tau * rho :=
  hc.tau_rho.symm

theorem t_mem_O (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t ∈ ctxO t tau x₁ x₂ := by
  have h : t ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_rho]; exact subset_closure (by simp)
  exact h.1

theorem tau_mem_O (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : tau ∈ ctxO t tau x₁ x₂ := by
  have h : tau ∈ ctxCO t tau x₁ x₂ rho := by
    rw [hc.CO_rho]; exact subset_closure (by simp)
  exact h.1

theorem O_le_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : ctxO t tau x₁ x₂ ≤ ctxM t tau x₁ x₂ := by
  rw [hc.O_eq_CV]; exact inf_le_left

theorem Q_le_O (hc : Ctx4Q t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxO t tau x₁ x₂ := by
  rw [hc.O_eq_Q]; exact le_sup_left

theorem Q_le_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) :
    ctxQ t tau x₁ x₂ rho ≤ ctxM t tau x₁ x₂ :=
  hc.normal_Q.1

theorem rho_mem_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : rho ∈ ctxM t tau x₁ x₂ := by
  rw [hc.M_eq]; exact mem_sup_right (subset_closure (by simp))

theorem lam_mem_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : lam ∈ ctxM t tau x₁ x₂ := by
  rw [hc.M_eq]; exact mem_sup_right (subset_closure (by simp))

theorem t_mem_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t ∈ ctxM t tau x₁ x₂ :=
  hc.O_le_M hc.t_mem_O

theorem tau_mem_M (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : tau ∈ ctxM t tau x₁ x₂ :=
  hc.O_le_M hc.tau_mem_O

theorem x₁_mem_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₁ ∈ ctxQ t tau x₁ x₂ rho :=
  hc.base_le_Q (subset_closure (by simp))

theorem x₂_mem_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₂ ∈ ctxQ t tau x₁ x₂ rho :=
  hc.base_le_Q (subset_closure (by simp))

theorem x₁_comm_x₂ (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₁ * x₂ = x₂ * x₁ :=
  hc.wreath.comm

theorem x₁_pow_four (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₁ ^ 4 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (by rw [hc.wreath.ord_x₁])

theorem x₂_pow_four (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₂ ^ 4 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (by rw [hc.wreath.ord_x₂])

theorem y_sq (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : (x₁ ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]; exact hc.x₁_pow_four

theorem z_sq (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : ((x₁ * x₂) ^ 2) ^ 2 = 1 := by
  rw [← pow_mul, show 2 * 2 = 4 from rfl, Commute.mul_pow hc.x₁_comm_x₂, hc.x₁_pow_four,
    hc.x₂_pow_four, one_mul]

theorem x₂_sq_sq (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : (x₂ ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]; exact hc.x₂_pow_four

theorem y_ne_one (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₁ ^ 2 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hc.wreath.ord_x₁]; norm_num)

theorem x₂_sq_ne_one (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₂ ^ 2 ≠ 1 :=
  pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hc.wreath.ord_x₂]; norm_num)

theorem y_ne_x₂_sq (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₁ ^ 2 ≠ x₂ ^ 2 := fun h => by
  have h1 : x₁ ^ 2 ∈ zpowers x₁ ⊓ zpowers x₂ :=
    ⟨pow_mem (mem_zpowers x₁) 2, h ▸ pow_mem (mem_zpowers x₂) 2⟩
  rw [hc.wreath.inf_eq_bot] at h1
  exact hc.y_ne_one (mem_bot.mp h1)

theorem x₂_sq (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : x₂ ^ 2 = x₁ ^ 2 * (x₁ * x₂) ^ 2 := by
  rw [Commute.mul_pow hc.x₁_comm_x₂, ← mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl,
    hc.x₁_pow_four, one_mul]

theorem V_le_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) :
    fourGrp x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho := by
  rw [fourGrp, closure_le]
  rintro _ (rfl | rfl)
  · exact pow_mem hc.x₁_mem_Q 2
  · exact pow_mem (mul_mem hc.x₁_mem_Q hc.x₂_mem_Q) 2

private theorem mem_cent_rho {a : G} (h : rho * a = a * rho) : a ∈ centralizer ({rho} : Set G) :=
  mem_centralizer_iff.mpr fun h' hh => by rw [Set.mem_singleton_iff.mp hh]; exact h

private theorem not_mem_Q_of {a : G} (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
    (h : rho * a = a * rho) (ha : a ≠ 1) : a ∉ ctxQ t tau x₁ x₂ rho := fun hQ => by
  have h2 : a ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hQ, mem_cent_rho h⟩
  rw [hc.CQ_rho] at h2
  exact ha (mem_bot.mp h2)

theorem t_not_mem_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : t ∉ ctxQ t tau x₁ x₂ rho :=
  not_mem_Q_of hc hc.rho_comm_t hc.t_ne_one

theorem tau_not_mem_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) : tau ∉ ctxQ t tau x₁ x₂ rho :=
  not_mem_Q_of hc hc.rho_comm_tau hc.tau_ne_one

theorem ttau_not_mem_Q (hc : Ctx4Q t L S x₁ x₂ lam rho tau) :
    t * tau ∉ ctxQ t tau x₁ x₂ rho := by
  refine not_mem_Q_of hc ?_ ?_
  · rw [← mul_assoc, hc.rho_comm_t, mul_assoc, hc.rho_comm_tau, ← mul_assoc]
  · intro h
    exact hc.t_ne_tau (by
      have h1 : tau = t⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h1, inv_eq_of_mul_eq_one_right hc.t_mul_self])

end Ctx4Q

end CFSG.OddStandard.SmallF3.HarrisU33
