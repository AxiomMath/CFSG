module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbL34S5g0

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34E

open Subgroup
open CFSG.OddStandard.SmallF3.HarrisU33.L34 CFSG.OddStandard.SmallF3.HarrisU33.L34Z

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}


private theorem mem_normalizer_of_conj_sub_mem {W : Subgroup G} {g : G}
    (h : ∀ w ∈ W, g * w * g⁻¹ ∈ W) : g ∈ Subgroup.normalizer (W : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ (le_of_eq ?_)
  · rw [Subgroup.map_le_iff_le_comap]
    intro w hw
    simpa using h w hw
  · exact (Subgroup.card_map_of_injective (MulAut.conj g).injective).symm

private theorem normalizer_zpowers_of_conj_mem {ρ g : G}
    (h : g * ρ * g⁻¹ ∈ Subgroup.zpowers ρ) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers ρ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_sub_mem ?_
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [(conj_zpow (a := g) (b := ρ) (i := k)).symm]
  exact (Subgroup.zpowers ρ).zpow_mem h k

private theorem conj_mem_T_of_conj_rho (hc : Ctx4Q t L S x₁ x₂ lam rho tau) {x : G}
    (hx : x ∈ ctxLO t tau x₁ x₂) (hxrho : x⁻¹ * rho * x ∈ zpowers rho) {d : G}
    (hd : d ∈ closure ({t, tau} : Set G)) :
    x * d * x⁻¹ ∈ closure ({t, tau} : Set G) := by
  have hdO : d ∈ ctxO t tau x₁ x₂ := by
    rw [hc.O_eq_Q]
    exact Subgroup.mem_sup_right hd
  have hxdO : x * d * x⁻¹ ∈ ctxO t tau x₁ x₂ :=
    (Subgroup.mem_normalizer_iff.mp hx d).mp hdO
  have hcd : Commute rho d := rho_comm_T hc d hd
  have hcommd : Commute d (x⁻¹ * rho * x) := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hxrho
    rw [← hi]
    exact hcd.symm.zpow_right i
  have hcentral : x * d * x⁻¹ ∈ Subgroup.centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x * d * x⁻¹) * rho = x * (d * (x⁻¹ * rho * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * rho * x) * d) * x⁻¹ := by rw [hcommd.eq]
      _ = rho * (x * d * x⁻¹) := by group
  have hCO : x * d * x⁻¹ ∈ ctxCO t tau x₁ x₂ rho := ⟨hxdO, hcentral⟩
  rwa [hc.CO_rho] at hCO

private theorem conj_mem_X_of_conj_rho (hc : Ctx4Q t L S x₁ x₂ lam rho tau)
    (hs : IsSylSL34 (ctxQ t tau x₁ x₂ rho)) {x : G} (hx : x ∈ ctxLO t tau x₁ x₂)
    (hxrho : x⁻¹ * rho * x ∈ zpowers rho) :
    ∀ h ∈ ctxX t tau x₁ x₂, x * h * x⁻¹ ∈ ctxX t tau x₁ x₂ := by
  have hTX : closure ({t, tau} : Set G) ≤ ctxX t tau x₁ x₂ := by
    rw [ctxX]
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  have hVX : fourGrp x₁ x₂ ≤ ctxX t tau x₁ x₂ := by
    rw [fourGrp, ctxX]
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> simp
  intro h hh
  rw [ctxX] at hh ⊢
  induction hh using Subgroup.closure_induction with
  | mem s hsx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
      rcases hsx with rfl | rfl | rfl | rfl
      · exact hTX (conj_mem_T_of_conj_rho hc hx hxrho (Subgroup.subset_closure (by simp)))
      · exact hTX (conj_mem_T_of_conj_rho hc hx hxrho (Subgroup.subset_closure (by simp)))
      · exact hVX (conj_V_of_mem_LO hc hs hx (Subgroup.subset_closure (by simp)))
      · exact hVX (conj_V_of_mem_LO hc hs hx (Subgroup.subset_closure (by simp)))
  | one => simp
  | mul a b _ _ iha ihb =>
      rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
      exact mul_mem iha ihb
  | inv a _ iha =>
      rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
      exact inv_mem iha

theorem mem_M_of_conj_rho (ha : Ctx4A t L S x₁ x₂ lam rho tau) {c : G}
    (hcL : c ∈ ctxLO t tau x₁ x₂) (hc : c * rho * c⁻¹ ∈ zpowers rho) :
    c ∈ ctxM t tau x₁ x₂ := by
  have hcq := ha.toCtx4L.toCtx4Q
  have hs := isSylSL34_of_Ctx4L ha.toCtx4L
  have hcN : c ∈ Subgroup.normalizer ((zpowers rho : Subgroup G) : Set G) :=
    normalizer_zpowers_of_conj_mem hc
  have hcinv_rho : c⁻¹ * rho * c ∈ zpowers rho :=
    (Subgroup.mem_normalizer_iff''.mp hcN rho).mp (Subgroup.mem_zpowers rho)
  have hfwd := conj_mem_X_of_conj_rho hcq hs hcL hcinv_rho
  have hcinv_rho' : (c⁻¹)⁻¹ * rho * c⁻¹ ∈ zpowers rho := by simpa using hc
  have hbwd := conj_mem_X_of_conj_rho hcq hs (inv_mem hcL) hcinv_rho'
  rw [ctxM, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hfwd h, fun hh => ?_⟩
  have h' := hbwd (c * h * c⁻¹) hh
  have heq : c⁻¹ * (c * h * c⁻¹) * (c⁻¹)⁻¹ = h := by group
  rwa [heq] at h'

end CFSG.OddStandard.SmallF3.HarrisU33.L34E
