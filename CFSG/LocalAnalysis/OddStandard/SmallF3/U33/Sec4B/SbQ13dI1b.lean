module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13dI1a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d1c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private lemma q13d_I_tau_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∈ q13E0 t tau x₁ x₂ rho om :=
  q13d_N_le_E0 h (q13b_tau_mem_N h)

private lemma q13d_I_mul_t (h : Q13Om t L S x₁ x₂ lam rho tau om) {a : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho) : a * t = t * a⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (q13a_t_mul_self h)
  have hconj : t * a * t = a⁻¹ := by simpa [htinv] using q13a_t_inv_A h a ha
  calc a * t = (t * t) * a * t := by rw [q13a_t_mul_self h, one_mul]
    _ = t * (t * a * t) := by group
    _ = t * a⁻¹ := by rw [hconj]

private lemma q13d_I_mul_t_mul (h : Q13Om t L S x₁ x₂ lam rho tau om) {a c' : G}
    (ha : a ∈ q13A t tau x₁ x₂ rho)
    (hc' : c' ∈ closure ({tau, om} : Set G)) :
    ∃ p ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)), a * (t * c') = t * p := by
  refine ⟨a⁻¹ * c', ?_, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_left (Subgroup.inv_mem _ ha)) (Subgroup.mem_sup_right hc')
  · calc a * (t * c') = (a * t) * c' := by group
      _ = (t * a⁻¹) * c' := by rw [q13d_I_mul_t h ha]
      _ = t * (a⁻¹ * c') := by group

theorem q13d_I_P1_le_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)) ≤ q13E0 t tau x₁ x₂ rho om := by
  refine sup_le ?_ ?_
  · rw [q13d_E0_eq_AC h]; exact le_sup_left
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact q13d_I_tau_mem_E0 h
    · exact q13d_om_mem_E0 h

theorem q13d_I_relIndex (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} : Set G)) :
    (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)).relIndex (q13E0 t tau x₁ x₂ rho om)
      = 2 := by
  have hle := q13d_I_P1_le_E0 h
  have hcard := Subgroup.relIndex_mul_card
    (H := q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G))
    (K := q13E0 t tau x₁ x₂ rho om)
  rw [inf_eq_left.mpr hle, q13d_I_card_P1 h hI, q13d_card_E0 h] at hcard
  have hpow : (2 : ℕ) ^ 7 = 2 * 2 ^ 6 := by norm_num
  rw [hpow] at hcard
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hcard

theorem q13d_I_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hI : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = closure ({tau, om} :
        Set G)) {x : G} :
    x ∈ q13E0 t tau x₁ x₂ rho om ↔ x ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G))
      ∨ ∃ p ∈ (q13A t tau x₁ x₂ rho ⊔ closure ({tau, om} : Set G)), x = t * p := by
  constructor
  · intro hx
    rw [q13d_E0_eq_AC h] at hx
    rw [mem_sup_iff_of_normalizes (q13d_CO_norm_A h)] at hx
    obtain ⟨a, ha, c, hc, rfl⟩ := hx
    rcases q13a_D8_cases h hc with hc | hc | hc | hc | hc | hc | hc | hc
    · left; rw [hc, mul_one]; exact Subgroup.mem_sup_left ha
    · left; rw [hc]
      exact mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · right
      simpa [hc] using q13d_I_mul_t_mul h ha
        (Subgroup.one_mem (closure ({tau, om} : Set G)))
    · right
      simpa [hc] using q13d_I_mul_t_mul h ha
        (Subgroup.subset_closure (by simp : tau ∈ ({tau, om} : Set G)))
    · left; rw [hc]
      exact mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    · left; rw [hc]
      exact mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))))
    · right
      simpa [hc] using q13d_I_mul_t_mul h ha
        (Subgroup.subset_closure (by simp : om ∈ ({tau, om} : Set G)))
    · right
      rw [hc]; rw [show t * om * tau = t * (om * tau) from by group]
      simpa only [mul_assoc] using q13d_I_mul_t_mul h ha
        (mul_mem (Subgroup.subset_closure (by simp : om ∈ ({tau, om} : Set G)))
          (Subgroup.subset_closure (by simp : tau ∈ ({tau, om} : Set G))))
  · rintro (hx | ⟨p, hp, rfl⟩)
    · exact q13d_I_P1_le_E0 h hx
    · exact mul_mem (q13d_t_mem_E0 h) (q13d_I_P1_le_E0 h hp)

private lemma q13d_I_E0_le_cent_y (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13E0 t tau x₁ x₂ rho om ≤ centralizer ({x₁ ^ 2} : Set G) := by
  rw [q13d_E0_eq_AC h]
  refine sup_le ?_ ?_
  · intro a ha
    change a ∈ centralizer ({x₁ ^ 2} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact q13a_A_comm h a ha (x₁ ^ 2)
      (q13a_V_le_A h (q13a_x₁_facts h).2.2.2.2.1)
  · rw [Subgroup.closure_le]
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hct | hco
    · rw [hct]
      change t ∈ centralizer ({x₁ ^ 2} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact q13a_X_comm h t (Subgroup.subset_closure (by simp)) (x₁ ^ 2)
        (Subgroup.subset_closure (by simp))
    · rw [hco]
      change om ∈ centralizer ({x₁ ^ 2} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (q13a_om_comm h).2.2 (x₁ ^ 2) (q13a_x₁_facts h).2.2.2.2.1

theorem q13d_lam_not_mem_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    lam ∉ q13E0 t tau x₁ x₂ rho om := by
  intro hlam
  have hcomm : lam ∈ centralizer ({x₁ ^ 2} : Set G) := q13d_I_E0_le_cent_y h hlam
  rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
  exact q13c_lam_not_cent_y h hcomm

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
