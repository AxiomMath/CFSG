module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13e6a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def q13R (t tau x₁ x₂ rho om : G) : Subgroup G where
  carrier := {b | b ∈ q13B t tau x₁ x₂ rho om ∧
    b * (t * om) * b⁻¹ * (t * om)⁻¹ ∈ fourGrp x₁ x₂}
  mul_mem' := by
    rintro a b ⟨ha, hav⟩ ⟨hb, hbv⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := closure_mono (Set.subset_insert _ _)
    have hc : (b * (t * om) * b⁻¹ * (t * om)⁻¹) * a = a * (b * (t * om) * b⁻¹ * (t * om)⁻¹) :=
      (mem_centralizer_iff.mp (mem_inf.mp ha).2) _ (hVN hbv)
    have e : a * b * (t * om) * (a * b)⁻¹ * (t * om)⁻¹ =
        (b * (t * om) * b⁻¹ * (t * om)⁻¹) * (a * (t * om) * a⁻¹ * (t * om)⁻¹) := by
      calc a * b * (t * om) * (a * b)⁻¹ * (t * om)⁻¹
          = (a * (b * (t * om) * b⁻¹ * (t * om)⁻¹)) * (t * om) * a⁻¹ * (t * om)⁻¹ := by group
        _ = ((b * (t * om) * b⁻¹ * (t * om)⁻¹) * a) * (t * om) * a⁻¹ * (t * om)⁻¹ := by rw [← hc]
        _ = (b * (t * om) * b⁻¹ * (t * om)⁻¹) * (a * (t * om) * a⁻¹ * (t * om)⁻¹) := by group
    rw [e]
    exact mul_mem hbv hav
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, hav⟩
    refine ⟨inv_mem ha, ?_⟩
    have hVN : fourGrp x₁ x₂ ≤ ctxN tau x₁ x₂ := closure_mono (Set.subset_insert _ _)
    have hc : Commute (a * (t * om) * a⁻¹ * (t * om)⁻¹) a :=
      (mem_centralizer_iff.mp (mem_inf.mp ha).2) _ (hVN hav)
    have e : a⁻¹ * (t * om) * a⁻¹⁻¹ * (t * om)⁻¹ = (a * (t * om) * a⁻¹ * (t * om)⁻¹)⁻¹ := by
      calc a⁻¹ * (t * om) * a⁻¹⁻¹ * (t * om)⁻¹
          = a⁻¹ * ((a * (t * om) * a⁻¹ * (t * om)⁻¹)⁻¹ * a) := by group
        _ = a⁻¹ * (a * (a * (t * om) * a⁻¹ * (t * om)⁻¹)⁻¹) := by rw [hc.inv_left.eq]
        _ = (a * (t * om) * a⁻¹ * (t * om)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hav


variable [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem q13e_mem_R {b : G} :
    b ∈ q13R t tau x₁ x₂ rho om ↔
      b ∈ q13B t tau x₁ x₂ rho om ∧ b * (t * om) * b⁻¹ * (t * om)⁻¹ ∈ fourGrp x₁ x₂ :=
  Iff.rfl

theorem q13e_R_le_B : q13R t tau x₁ x₂ rho om ≤ q13B t tau x₁ x₂ rho om := by
  intro b hb
  exact hb.1

theorem q13e_P_le_R (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    q13P t tau x₁ x₂ rho om ≤ q13R t tau x₁ x₂ rho om := by
  intro p hp
  have hgp : t * om ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
  have hB : p ∈ q13B t tau x₁ x₂ rho om := hD.E0_le_B (q13d_P_le_E0 h hp)
  refine ⟨hB, ?_⟩
  have hc : p * (t * om) = (t * om) * p := q13d_P_comm h hD.A_cent p hp (t * om) hgp
  rw [show p * (t * om) * p⁻¹ * (t * om)⁻¹ = 1 by rw [hc]; group]
  exact (fourGrp x₁ x₂).one_mem

theorem q13e_R_inf_E0 (h : Q13Om t L S x₁ x₂ lam rho tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ e ∈ q13R t tau x₁ x₂ rho om, e ∈ q13E0 t tau x₁ x₂ rho om → e ∈ q13P t tau x₁ x₂ rho om := by
  intro e he he0
  have heconj : e * (t * om) * e⁻¹ * (t * om)⁻¹ ∈ fourGrp x₁ x₂ := (q13e_mem_R.mp he).2
  rcases (q13d_mem_E0 h hD.A_cent).mp he0 with hp | ⟨p, hp, rfl⟩
  · exact hp
  · exfalso
    have hgp : t * om ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
    have hpc : p * (t * om) * p⁻¹ = t * om := by
      rw [q13d_P_comm h hD.A_cent p hp (t * om) hgp]
      group
    have hval : (t * p) * (t * om) * (t * p)⁻¹ * (t * om)⁻¹ = tau := by
      rw [show (t * p) * (t * om) * (t * p)⁻¹ * (t * om)⁻¹
            = t * (p * (t * om) * p⁻¹) * t⁻¹ * (t * om)⁻¹ by group, hpc,
          hD.t_inv_P (t * om) hgp]
      rw [show (t * om)⁻¹ * (t * om)⁻¹ = tau from by
        calc (t * om)⁻¹ * (t * om)⁻¹ = ((t * om) * (t * om))⁻¹ :=
              (mul_inv_rev (t * om) (t * om)).symm
          _ = ((t * om) ^ 2)⁻¹ := by rw [pow_two]
          _ = tau⁻¹ := by rw [hD.gam_sq]
          _ = tau := inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]
    rw [hval] at heconj
    exact l12_tau_not_mem_V h.c11.toCtx10.toCtx4 heconj

theorem q13e_f_R (h : Q13Om t L S x₁ x₂ lam rho tau om) (hC : Q13C t x₁ x₂ lam tau om)
    (hD : Q13D t x₁ x₂ lam rho tau om) :
    ∀ r ∈ q13R t tau x₁ x₂ rho om, (t * lam) * r * (t * lam)⁻¹ ∈ q13R t tau x₁ x₂ rho om := by
  intro r hr
  have hfL : t * lam ∈ q13L t tau x₁ x₂ rho om := q13e_f_mem_L h hD
  have hγP : t * om ∈ q13P t tau x₁ x₂ rho om := q13d_gam_mem_P h
  have hγinvP : (t * om)⁻¹ ∈ q13P t tau x₁ x₂ rho om := (q13P t tau x₁ x₂ rho om).inv_mem hγP
  have hfg : (t * lam) * (t * om) * (t * lam)⁻¹ = (t * om)⁻¹ := q13e_f_gam h hC
  have hfg' : (t * lam)⁻¹ * (t * om) * (t * lam) = (t * om)⁻¹ := by
    simpa [q13e_f_inv h] using hfg
  have hmul := q13e_comm_BP_mul_right h hD r hr.1 (t * om) hγP (t * om)⁻¹ hγinvP
  have h1 : r * ((t * om) * (t * om)⁻¹) * r⁻¹ * ((t * om) * (t * om)⁻¹)⁻¹ = 1 := by group
  rw [h1] at hmul
  simp only [inv_inv] at hmul
  have hφinv : r * (t * om)⁻¹ * r⁻¹ * (t * om) =
      (r * (t * om) * r⁻¹ * (t * om)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hmul.symm
  refine ⟨hD.B_normal.2 (t * lam) hfL r hr.1, ?_⟩
  have hkey : (t * lam) * r * (t * lam)⁻¹ * (t * om) * ((t * lam) * r * (t * lam)⁻¹)⁻¹ *
        (t * om)⁻¹ = (t * lam) * (r * (t * om)⁻¹ * r⁻¹ * (t * om)) * (t * lam)⁻¹ := by
    calc (t * lam) * r * (t * lam)⁻¹ * (t * om) * ((t * lam) * r * (t * lam)⁻¹)⁻¹ *
          (t * om)⁻¹
        = (t * lam) * (r * ((t * lam)⁻¹ * (t * om) * (t * lam)) * r⁻¹ *
            ((t * lam)⁻¹ * (t * om) * (t * lam))⁻¹) * (t * lam)⁻¹ := by group
      _ = (t * lam) * (r * (t * om)⁻¹ * r⁻¹ * ((t * om)⁻¹)⁻¹) * (t * lam)⁻¹ := by rw [hfg']
      _ = (t * lam) * (r * (t * om)⁻¹ * r⁻¹ * (t * om)) * (t * lam)⁻¹ := by rw [inv_inv]
  rw [hkey, hφinv]
  exact q13e_f_V h _ ((fourGrp x₁ x₂).inv_mem hr.2)

theorem q13e_card_R (h : Q13Om t L S x₁ x₂ lam rho tau om) (hB : Q13Bs t x₁ x₂ lam tau)
    (hC : Q13C t x₁ x₂ lam tau om) (hD : Q13D t x₁ x₂ lam rho tau om) :
    Nat.card (q13R t tau x₁ x₂ rho om) = 2 ^ 8 := by
  have hcard := q13e_card_mul_eq_of_hom_mod
    (K := q13B t tau x₁ x₂ rho om) (H := q13R t tau x₁ x₂ rho om)
    (P' := ctxN tau x₁ x₂) (N' := fourGrp x₁ x₂)
    (φ := fun b => b * (t * om) * b⁻¹ * (t * om)⁻¹)
    (q13e_R_le_B (t := t) (tau := tau) (x₁ := x₁) (x₂ := x₂) (rho := rho) (om := om))
    (q13b_V_le_N h)
    (by
      intro p hp n hn
      have hpn : p * n = n * p :=
        CFSG.Open.IsElemAbelian.comm (q13b_N_elemAbelian h) hp (q13b_V_le_N h hn)
      have h : p * n * p⁻¹ = n := by rw [hpn]; group
      rwa [h])
    (by
      intro b hb
      exact q13e_comm_BP h hD b hb (t * om) (q13d_gam_mem_P h))
    (by
      intro b hb b' hb'
      rw [q13e_comm_BP_mul_left h hD b hb b' hb' (t * om) (q13d_gam_mem_P h)]
      have h : (b * (t * om) * b⁻¹ * (t * om)⁻¹) * (b' * (t * om) * b'⁻¹ * (t * om)⁻¹) *
          ((b * (t * om) * b⁻¹ * (t * om)⁻¹) *
            (b' * (t * om) * b'⁻¹ * (t * om)⁻¹))⁻¹ = 1 := by group
      rw [h]
      exact (fourGrp x₁ x₂).one_mem)
    (by
      intro b hb
      rw [q13e_mem_R]
      exact ⟨fun hv => ⟨hb, hv⟩, fun hh => hh.2⟩)
    (by
      intro p hp
      rcases (q13d_mem_N h).mp hp with hV | ⟨v, hv, rfl⟩
      · refine ⟨1, (q13B t tau x₁ x₂ rho om).one_mem, ?_⟩
        simpa using (fourGrp x₁ x₂).inv_mem hV
      · refine ⟨t, hD.E0_le_B (q13d_t_mem_E0 h), ?_⟩
        have hφt : t * (t * om) * t⁻¹ * (t * om)⁻¹ = tau := by
          rw [q13e_comm_tP h hD (t * om) (q13d_gam_mem_P h)]
          rw [show ((t * om) ^ 2)⁻¹ = tau from by
            rw [hD.gam_sq, inv_eq_of_mul_eq_one_right (q13a_tau_mul_self h)]]
        rw [hφt]
        have hcomm : tau * v = v * tau :=
          CFSG.Open.IsElemAbelian.comm (q13b_N_elemAbelian h) (q13b_tau_mem_N h)
            (q13b_V_le_N h hv)
        have hcomminv : tau * v⁻¹ = v⁻¹ * tau := (show Commute tau v from hcomm).inv_right
        have hval : tau * (tau * v)⁻¹ = v⁻¹ := by
          calc tau * (tau * v)⁻¹ = tau * (v⁻¹ * tau⁻¹) := by group
            _ = (tau * v⁻¹) * tau⁻¹ := by group
            _ = (v⁻¹ * tau) * tau⁻¹ := by rw [hcomminv]
            _ = v⁻¹ := by group
        rw [hval]
        exact (fourGrp x₁ x₂).inv_mem hv)
  have hBcard : Nat.card (q13B t tau x₁ x₂ rho om) = 2 ^ 9 := q13e_card_B_eq h hB hC hD
  have hVcard : Nat.card (fourGrp x₁ x₂) = 4 := (h.c11.wreath.fourGrp_eq_omega).2.2
  have hNcard : Nat.card (ctxN tau x₁ x₂) = 8 := q13b_card_N h
  rw [hBcard, hVcard, hNcard] at hcard
  norm_num at hcard ⊢
  omega

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
