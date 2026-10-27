module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13d0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13d_gam_cent_A (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) :
    ∀ a ∈ q13A t tau x₁ x₂ rho, (t * om) * a = a * (t * om) := by
  have hgam : t * om ∈ closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [hII]
    exact Subgroup.mem_zpowers _
  have hcent := (Subgroup.mem_inf.mp hgam).2
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp hcent a ha).symm

theorem q13d_A_inf_gam (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ q13A t tau x₁ x₂ rho, g ∈ zpowers (t * om) → g = 1 := by
  have hmem : t * om ∈ closure ({t, om} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  intro g hgA hg
  exact q13d_A_inf_CO h g hgA (Subgroup.zpowers_le.mpr hmem hg)

theorem q13d_A_le_P (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    q13A t tau x₁ x₂ rho ≤ q13P t tau x₁ x₂ rho om :=
  le_sup_left

theorem q13d_gam_mem_P (_h : Q13Om t L S x₁ x₂ lam rho tau om) :
    t * om ∈ q13P t tau x₁ x₂ rho om :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem q13d_tau_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    tau ∈ q13P t tau x₁ x₂ rho om := by
  rw [← q13d_gam_sq h]
  exact Subgroup.mem_sup_right (by simpa using Subgroup.zpow_mem_zpowers (t * om) 2)

theorem q13d_N_le_P (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ q13P t tau x₁ x₂ rho om := by
  rw [ctxN, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact q13d_tau_mem_P h
  · exact q13d_A_le_P h (q13a_V_le_A h (Subgroup.subset_closure (by simp)))
  · exact q13d_A_le_P h (q13a_V_le_A h (Subgroup.subset_closure (by simp)))

theorem q13d_mem_P (h : Q13Om t L S x₁ x₂ lam rho tau om)
    (hII : closure ({t, om} : Set G) ⊓
      centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) = zpowers (t * om)) {p : G} :
    p ∈ q13P t tau x₁ x₂ rho om ↔ ∃ a ∈ q13A t tau x₁ x₂ rho, ∃ k : ℤ, p = a * (t * om) ^ k := by
  have hcent : t * om ∈ centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    have hgam : t * om ∈ closure ({t, om} : Set G) ⊓
        centralizer ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [hII]
      exact Subgroup.mem_zpowers _
    exact (Subgroup.mem_inf.mp hgam).2
  have hnorm : ∀ k ∈ zpowers (t * om), ∀ a ∈ q13A t tau x₁ x₂ rho,
      k * a * k⁻¹ ∈ q13A t tau x₁ x₂ rho := by
    intro k hk a ha
    have hk' : k ∈ Subgroup.centralizer
        ((q13A t tau x₁ x₂ rho : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hcent hk
    have hcomm : a * k = k * a := Subgroup.mem_centralizer_iff.mp hk' a ha
    have hka : k * a * k⁻¹ = a := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hka]
    exact ha
  constructor
  · intro hp
    obtain ⟨a, ha, k, hk, hp⟩ :=
      (mem_sup_iff_of_normalizes (H := q13A t tau x₁ x₂ rho)
        (K := zpowers (t * om)) hnorm).mp hp
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact ⟨a, ha, m, by rw [hp, hm]⟩
  · rintro ⟨a, ha, k, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
