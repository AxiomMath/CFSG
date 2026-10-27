module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP0d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12f
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13a0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13b_isPGroup_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    IsPGroup 2 (ctxU t tau x₁ x₂ lam) :=
  h.c11.U_sylow.2.1

theorem q13b_card_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxU t tau x₁ x₂ lam) = 2 ^ 10 :=
  p0_card_U (ctx8e_of_ctx11 h.c11).toCtx8d.toCtx8c.toCtx8b

theorem q13b_U_le_M (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxU t tau x₁ x₂ lam ≤ ctxM t tau x₁ x₂ :=
  h.c11.U_sylow.1

theorem q13b_O_le_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxO t tau x₁ x₂ ≤ ctxU t tau x₁ x₂ lam :=
  le_sup_left

theorem q13b_S_lt_U (h : Q13Om t L S x₁ x₂ lam rho tau om) : S < ctxU t tau x₁ x₂ lam := by
  refine lt_of_le_of_ne h.c11.S_le_U ?_
  intro hSU
  have hS := Ctx4.card_S_seven h.c11.toCtx10.toCtx4
  have hU := q13b_card_U h
  rw [hSU, hU] at hS
  norm_num at hS

theorem q13b_t_mem_O (h : Q13Om t L S x₁ x₂ lam rho tau om) : t ∈ ctxO t tau x₁ x₂ :=
  h.c11.R_le_O (h.c11.X_le_R (Subgroup.subset_closure (by simp)))

theorem q13b_om_mem_O (h : Q13Om t L S x₁ x₂ lam rho tau om) : om ∈ ctxO t tau x₁ x₂ :=
  (Subgroup.mem_inf.mp h.om_mem).1

theorem q13b_tau_mem_N (h : Q13Om t L S x₁ x₂ lam rho tau om) : tau ∈ ctxN tau x₁ x₂ :=
  Subgroup.subset_closure (by simp)

theorem q13b_V_le_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ :=
  (p0_V_le_N_le_X t tau x₁ x₂).1

theorem q13b_N_le_O (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxN tau x₁ x₂ ≤ ctxO t tau x₁ x₂ :=
  ((p0_V_le_N_le_X t tau x₁ x₂).2.trans h.c11.X_le_R).trans h.c11.R_le_O

theorem q13b_V_le_O (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    fourGrp x₁ x₂ ≤ ctxO t tau x₁ x₂ :=
  (q13b_V_le_N h).trans (q13b_N_le_O h)

theorem q13b_N_elemAbelian (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    CFSG.Open.IsElemAbelian 2 (ctxN tau x₁ x₂) :=
  CFSG.Open.IsElemAbelian.mono (Ctx4.ctxX_facts h.c11.toCtx10.toCtx4).1
    (p0_V_le_N_le_X t tau x₁ x₂).2

theorem q13b_card_N (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(ctxN tau x₁ x₂) = 8 := by
  have hN_eq : ctxN tau x₁ x₂ = fourGrp x₁ x₂ ⊔ zpowers tau := by
    refine le_antisymm ?_ ?_
    · rw [ctxN, Subgroup.closure_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h1 | h1 | h1
      · rw [h1]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers tau)
      · rw [h1]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · rw [h1]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · refine sup_le (p0_V_le_N_le_X t tau x₁ x₂).1 ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hτM : tau ∈ ctxM t tau x₁ x₂ := (q13a_mem_M h).2.1
  have hτnorm : tau ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    exact ⟨fun hv => h.c11.normal_V.2 tau hτM v hv, fun hv => by
      have hmem := h.c11.normal_V.2 tau⁻¹ ((ctxM t tau x₁ x₂).inv_mem hτM)
        (tau * v * tau⁻¹) hv
      have heq : tau⁻¹ * (tau * v * tau⁻¹) * (tau⁻¹)⁻¹ = v := by group
      rwa [heq] at hmem⟩
  have hnorm : ∀ k ∈ zpowers tau, ∀ v ∈ fourGrp x₁ x₂, k * v * k⁻¹ ∈ fourGrp x₁ x₂ := by
    intro k hk v hv
    have hk' : k ∈ Subgroup.normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hτnorm hk
    exact (Subgroup.mem_normalizer_iff.mp hk' v).mp hv
  have hdis : fourGrp x₁ x₂ ⊓ zpowers tau = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxV, hxT⟩ := hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxT
    have h2 : (orderOf tau : ℤ) = 2 := by
      rw [(Ctx4.m12Rel h.c11.toCtx10.toCtx4).ord_tau]; norm_num
    have hkm : tau ^ (k % 2) = x := by
      have hh := zpow_mod_orderOf tau k
      rw [h2] at hh
      exact hh.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hkm
      exact hkm.symm
    · rw [h1, zpow_one] at hkm
      exact absurd (hkm.symm ▸ hxV) (l12_tau_not_mem_V h.c11.toCtx10.toCtx4)
  have hcardV : Nat.card ↥(fourGrp x₁ x₂) = 4 := h.c11.wreath.fourGrp_eq_omega.2.2
  have hcardT : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers, (Ctx4.m12Rel h.c11.toCtx10.toCtx4).ord_tau]
  rw [hN_eq, card_sup_eq_mul hnorm hdis, hcardV, hcardT]

theorem q13b_V_normal_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    NormalIn (fourGrp x₁ x₂) (ctxU t tau x₁ x₂ lam) :=
  ⟨(q13b_V_le_O h).trans (q13b_O_le_U h), fun g hg k hk =>
    h.c11.normal_V.2 g (q13b_U_le_M h hg) k hk⟩

theorem q13b_N_normal_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxN tau x₁ x₂) (ctxU t tau x₁ x₂ lam) :=
  ⟨(q13b_N_le_O h).trans (q13b_O_le_U h), fun g hg k hk =>
    h.c11.normal_N.2 g (q13b_U_le_M h hg) k hk⟩

theorem q13b_Q_normal_U (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxQ t tau x₁ x₂ rho) (ctxU t tau x₁ x₂ lam) :=
  ⟨((l12_Q_le_R h.c11).trans h.c11.R_le_O).trans (q13b_O_le_U h), fun g hg k hk =>
    h.c11.normal_Q.2 g (q13b_U_le_M h hg) k hk⟩

theorem q13b_O_cent_V (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ o ∈ ctxO t tau x₁ x₂, ∀ v ∈ fourGrp x₁ x₂, o * v = v * o := by
  intro o ho v hv
  have hv' : v ∈ ctxO t tau x₁ x₂ ⊓
      centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) := by
    rw [h.c11.center_O]
    exact hv
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv').2) o ho

theorem q13b_O_eq (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ctxO t tau x₁ x₂ = ctxQ t tau x₁ x₂ rho ⊔ ctxCO t tau x₁ x₂ rho := by
  have htCO : t ∈ ctxCO t tau x₁ x₂ rho :=
    ⟨q13b_t_mem_O h, Subgroup.mem_centralizer_singleton_iff.mpr (q13a_t_comm h).2.1⟩
  have htauCO : tau ∈ ctxCO t tau x₁ x₂ rho :=
    ⟨q13b_N_le_O h (q13b_tau_mem_N h),
      Subgroup.mem_centralizer_singleton_iff.mpr h.c11.tau_rho⟩
  have hTle : closure ({t, tau} : Set G) ≤ ctxCO t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact htCO
    · exact htauCO
  refine le_antisymm ?_ ?_
  · rw [h.c11.O_eq]
    have hRle : ctxR t tau x₁ x₂ ≤ ctxQ t tau x₁ x₂ rho ⊔ ctxCO t tau x₁ x₂ rho := by
      rw [l12_R_eq h.c11]
      exact sup_le le_sup_left (hTle.trans le_sup_right)
    exact sup_le hRle le_sup_right
  · exact sup_le ((l12_Q_le_R h.c11).trans h.c11.R_le_O) (by rw [ctxCO]; exact inf_le_left)

theorem q13b_Q_inf_CO (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    ∀ g ∈ ctxQ t tau x₁ x₂ rho, g ∈ ctxCO t tau x₁ x₂ rho → g = 1 := by
  intro g hgQ hgCO
  have hcomm : g * rho = rho * g :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hgCO).2
  exact l12_cent_Q_rho h.c11 g hgQ hcomm

theorem q13b_z_facts (h : Q13Om t L S x₁ x₂ lam rho tau om) :
    (x₁ * x₂) ^ 2 ≠ 1 ∧ (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 :=
  ⟨h.c11.wreath.sq_x₁x₂_ne_one, h.c11.wreath.sq_x₁x₂_mul_self⟩

theorem q13b_tau_ne_one (h : Q13Om t L S x₁ x₂ lam rho tau om) : tau ≠ 1 := by
  intro h1
  exact l12_tau_not_mem_V h.c11.toCtx10.toCtx4 (h1.symm ▸ Subgroup.one_mem _)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
