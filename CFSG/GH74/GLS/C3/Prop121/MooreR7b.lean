module

public import CFSG.GH74.GLS.C3.Prop121.MooreR7

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2

namespace MCtx

variable {G : Type} [Group G] {n : ℕ} {x : G} {K Q : Subgroup G} {t u g : G} {L : Subgroup G}
  {φ : Perm (Fin (n + 1)) →* G}

theorem u1_inv_tg (h : MCtx n x K Q t u g L φ) :
    φ (cs n (n - 1)) * (g * t * g⁻¹) * (φ (cs n (n - 1)))⁻¹ = (g * t * g⁻¹)⁻¹ := by
  have hp : cs n (n - 1) * cEnd n * (cs n (n - 1))⁻¹ = (cEnd n)⁻¹ := by
    unfold cEnd
    rw [cs_inv, mul_inv_rev, cs_inv, cs_inv]
    calc cs n (n - 1) * (cs n (n - 2) * cs n (n - 1)) * cs n (n - 1)
        = cs n (n - 1) * cs n (n - 2) * (cs n (n - 1) * cs n (n - 1)) := by group
      _ = cs n (n - 1) * cs n (n - 2) := by rw [cs_mul_self, mul_one]
  have := congrArg φ hp
  rw [map_mul, map_mul, map_inv, map_inv, h.hc] at this
  exact this

theorem exists_sigma (h : MCtx n x K Q t u g L φ) :
    ∃ σ1 ∈ L ⊔ zpowers u, σ1 * σ1 = 1 ∧ σ1 ∉ L ∧
      σ1 * (g * t * g⁻¹) * σ1⁻¹ = (g * t * g⁻¹)⁻¹ ∧
      σ1 * (g * x * g⁻¹) = (g * x * g⁻¹) * σ1 ∧
      ∀ k, k + 4 ≤ n → σ1 * (g * φ (cs n k) * g⁻¹) = (g * φ (cs n k) * g⁻¹) * σ1 := by
  have hn5 := h.n_ge
  set U : G := φ (cs n (n - 1)) with hU
  have hU2 : U * U = 1 := by rw [hU, ← map_mul, cs_mul_self, map_one]
  have hU_t : U * t * U⁻¹ = t⁻¹ := h.odd_inv_t (sign_cs (by omega))
  have hU_tg : U * (g * t * g⁻¹) * U⁻¹ = (g * t * g⁻¹)⁻¹ := h.u1_inv_tg
  have hU_x : U * x = x * U := h.stab_comm_x (cs_apply_zero (by omega))
  have hU_a : ∀ k, k + 4 ≤ n → U * φ (cs n k) = φ (cs n k) * U := by
    intro k hk
    rw [hU, ← map_mul, ← map_mul, ← cs_comm n (by omega : k + 2 ≤ n - 1)]
  set b : G := g * U * g⁻¹ with hb
  have hb2 : b * b = 1 := by
    calc b * b = g * (U * U) * g⁻¹ := by rw [hb]; group
      _ = 1 := by rw [hU2]; group
  have hgi : g⁻¹ * t * g = g * t * g⁻¹ := by rw [h.g_inv]
  have hb_t : b * t * b⁻¹ = t⁻¹ := by
    calc b * t * b⁻¹ = g * U * (g⁻¹ * t * g) * U⁻¹ * g⁻¹ := by rw [hb]; group
      _ = g * (U * (g * t * g⁻¹) * U⁻¹) * g⁻¹ := by rw [hgi]; group
      _ = g * (g * t * g⁻¹)⁻¹ * g⁻¹ := by rw [hU_tg]
      _ = g * (g * t⁻¹ * g⁻¹) * g⁻¹ := by rw [show (g * t * g⁻¹)⁻¹ = g * t⁻¹ * g⁻¹ by group]
      _ = t⁻¹ := conj_conj_invol h.S.g_sq t⁻¹
  have hb_tg : b * (g * t * g⁻¹) * b⁻¹ = (g * t * g⁻¹)⁻¹ := by
    calc b * (g * t * g⁻¹) * b⁻¹ = g * (U * t * U⁻¹) * g⁻¹ := by rw [hb]; group
      _ = g * t⁻¹ * g⁻¹ := by rw [hU_t]
      _ = (g * t * g⁻¹)⁻¹ := by group
  have hb_x : b * (g * x * g⁻¹) = (g * x * g⁻¹) * b := by
    calc b * (g * x * g⁻¹) = g * (U * x) * g⁻¹ := by rw [hb]; group
      _ = g * (x * U) * g⁻¹ := by rw [hU_x]
      _ = (g * x * g⁻¹) * b := by rw [hb]; group
  have hb_a : ∀ k, k + 4 ≤ n →
      b * (g * φ (cs n k) * g⁻¹) = (g * φ (cs n k) * g⁻¹) * b := by
    intro k hk
    calc b * (g * φ (cs n k) * g⁻¹) = g * (U * φ (cs n k)) * g⁻¹ := by rw [hb]; group
      _ = g * (φ (cs n k) * U) * g⁻¹ := by rw [hU_a k hk]
      _ = (g * φ (cs n k) * g⁻¹) * b := by rw [hb]; group
  obtain ⟨i, l, hl, hbl⟩ := h.C.N_eq b hb_t
  have hlt : Commute l t := h.C.L_comm_t l hl
  have hσt : (l * u) * t * (l * u)⁻¹ = t⁻¹ := by
    have hlt' : l * t⁻¹ = t⁻¹ * l := hlt.inv_right
    calc (l * u) * t * (l * u)⁻¹ = l * (u * t * u⁻¹) * l⁻¹ := by group
      _ = l * t⁻¹ * l⁻¹ := by rw [h.S.u_inv_t]
      _ = t⁻¹ := by rw [hlt']; group
  have hσt_i : (l * u) * t ^ i * (l * u)⁻¹ = (t ^ i)⁻¹ := by
    calc (l * u) * t ^ i * (l * u)⁻¹ = ((l * u) * t * (l * u)⁻¹) ^ i := conj_zpow.symm
      _ = t⁻¹ ^ i := by rw [hσt]
      _ = (t ^ i)⁻¹ := inv_zpow t i
  have hbσ : b = t ^ i * (l * u) := by rw [hbl]; group
  have hσ2 : (l * u) * (l * u) = 1 := by
    have h1 : b * b = t ^ i * ((l * u) * t ^ i * (l * u)⁻¹) * ((l * u) * (l * u)) := by
      rw [hbσ]; group
    rw [hσt_i] at h1
    calc (l * u) * (l * u) = t ^ i * (t ^ i)⁻¹ * ((l * u) * (l * u)) := by group
      _ = b * b := h1.symm
      _ = 1 := hb2
  have hσY : l * u ∈ L ⊔ zpowers u :=
    mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers u))
  have hσL : l * u ∉ L := by
    intro hlu
    apply h.C.u_not_mem_L
    have := L.mul_mem (L.inv_mem hl) hlu
    simpa using this
  have hσ_eq : l * u = (t ^ i)⁻¹ * b := by rw [hbσ]; group
  have hti_tg : (t ^ i)⁻¹ * (g * t * g⁻¹)⁻¹ * t ^ i = (g * t * g⁻¹)⁻¹ := by
    have hc : Commute (t ^ i) ((g * t * g⁻¹)⁻¹) :=
      ((show Commute t (g * t * g⁻¹) from h.t_comm_tg).zpow_left i).inv_right
    have : (t ^ i) * (g * t * g⁻¹)⁻¹ = (g * t * g⁻¹)⁻¹ * (t ^ i) := hc
    rw [mul_assoc, ← this]; group
  refine ⟨l * u, hσY, hσ2, hσL, ?_, ?_, ?_⟩
  · calc (l * u) * (g * t * g⁻¹) * (l * u)⁻¹
        = (t ^ i)⁻¹ * (b * (g * t * g⁻¹) * b⁻¹) * t ^ i := by rw [hσ_eq]; group
      _ = (g * t * g⁻¹)⁻¹ := by rw [hb_tg, hti_tg]
  · have hc : Commute (t ^ i) (g * x * g⁻¹) :=
      (show Commute t (g * x * g⁻¹) from h.t_comm_xg).zpow_left i
    have hc' : Commute (t ^ i)⁻¹ (g * x * g⁻¹) := hc.inv_left
    calc (l * u) * (g * x * g⁻¹) = (t ^ i)⁻¹ * (b * (g * x * g⁻¹)) := by rw [hσ_eq]; group
      _ = (t ^ i)⁻¹ * ((g * x * g⁻¹) * b) := by rw [hb_x]
      _ = ((t ^ i)⁻¹ * (g * x * g⁻¹)) * b := by group
      _ = ((g * x * g⁻¹) * (t ^ i)⁻¹) * b := by rw [hc']
      _ = (g * x * g⁻¹) * (l * u) := by rw [hσ_eq]; group
  · intro k hk
    have haL : g * φ (cs n k) * g⁻¹ ∈ L := h.a_mem_L hk
    have hc : Commute (t ^ i) (g * φ (cs n k) * g⁻¹) :=
      ((show Commute t (g * φ (cs n k) * g⁻¹) from (h.C.L_comm_t _ haL).symm).zpow_left i)
    have hc' : Commute (t ^ i)⁻¹ (g * φ (cs n k) * g⁻¹) := hc.inv_left
    calc (l * u) * (g * φ (cs n k) * g⁻¹)
        = (t ^ i)⁻¹ * (b * (g * φ (cs n k) * g⁻¹)) := by rw [hσ_eq]; group
      _ = (t ^ i)⁻¹ * ((g * φ (cs n k) * g⁻¹) * b) := by rw [hb_a k hk]
      _ = ((t ^ i)⁻¹ * (g * φ (cs n k) * g⁻¹)) * b := by group
      _ = ((g * φ (cs n k) * g⁻¹) * (t ^ i)⁻¹) * b := by rw [hc']
      _ = (g * φ (cs n k) * g⁻¹) * (l * u) := by rw [hσ_eq]; group

end MCtx

end CFSG.GH74.GLS.C3.Prop121
