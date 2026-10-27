module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1b

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_E0_eq_AC (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13E0 t tau x₁ x₂ rho om = q13A t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
  rw [q13E0, q13P]
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left ?_) ?_
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_sup_right (mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))))
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  · refine sup_le (le_trans le_sup_left le_sup_left) ?_
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    · rw [hx]
      have ht : t ∈ q13A t tau x₁ x₂ rho ⊔ zpowers (t * om) ⊔ zpowers t :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      have hg : t * om ∈ q13A t tau x₁ x₂ rho ⊔ zpowers (t * om) ⊔ zpowers t :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers (t * om)))
      have h1 : t * (t * om) = om := by rw [← mul_assoc, q13a_t_mul_self h, one_mul]
      simpa only [h1, SetLike.mem_coe] using mul_mem ht hg

theorem q13d_card_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(q13E0 t tau x₁ x₂ rho om) = 2 ^ 7 := by
  rw [q13d_E0_eq_AC h]
  exact q13d_card_AC h

theorem q13d_E0_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam ⊓ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G)
      = q13E0 t tau x₁ x₂ rho om := by
  exact (q13d_cent_N_U_eq h).trans (q13d_E0_eq_AC h).symm

theorem q13d_E0_le_cent_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13E0 t tau x₁ x₂ rho om ≤ centralizer ((ctxN tau x₁ x₂ : Subgroup G) : Set G) := by
  rw [q13d_E0_eq_AC h]
  exact (q13d_AC_le_cent h).trans inf_le_right

theorem q13d_N_le_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ q13E0 t tau x₁ x₂ rho om := by
  rw [q13d_E0_eq_AC h, ctxN, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx
  · rw [hx]
    refine Subgroup.mem_sup_right ?_
    have ht : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
    have hom : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
    have hconj : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
      mul_mem (mul_mem hom ht) (inv_mem hom)
    have htau : tau = t * (om * t * om⁻¹) := by
      rw [h.t_om, ← mul_assoc, q13a_t_mul_self h, one_mul]
    rw [htau]
    exact mul_mem ht hconj
  · rw [hx]
    exact Subgroup.mem_sup_left (q13a_V_le_A h (Subgroup.subset_closure (by simp)))
  · rw [hx]
    exact Subgroup.mem_sup_left (q13a_V_le_A h (Subgroup.subset_closure (by simp)))

theorem q13d_X_le_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxX t tau x₁ x₂ ≤ q13E0 t tau x₁ x₂ rho om := by
  rw [ctxX, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx | hx | hx
  · rw [hx]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  · rw [hx]
    exact q13d_N_le_E0 h (q13b_tau_mem_N h)
  · rw [hx]
    exact q13d_N_le_E0 h (q13b_V_le_N h (Subgroup.subset_closure (by simp)))
  · rw [hx]
    exact q13d_N_le_E0 h (q13b_V_le_N h (Subgroup.subset_closure (by simp)))

theorem q13d_om_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    om ∈ q13E0 t tau x₁ x₂ rho om := by
  rw [q13d_E0_eq_AC h]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

theorem q13d_gam_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * om ∈ q13E0 t tau x₁ x₂ rho om := by
  rw [q13d_E0_eq_AC h]
  exact Subgroup.mem_sup_right
    (mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))

theorem q13d_P_le_E0 (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13P t tau x₁ x₂ rho om ≤ q13E0 t tau x₁ x₂ rho om :=
  le_sup_left

theorem q13d_t_mem_E0 (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t ∈ q13E0 t tau x₁ x₂ rho om :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
