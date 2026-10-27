module

public import CFSG.GH74.GLS.Stage4.T2NegFour

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

variable {G : Type} [Group G] {C₁ : Subgroup G} {z u : G} {K₁ K₂ H : Subgroup G} {w₁ w₂ : G}

theorem T2Four1.swap (h : T2Four1 C₁ z u K₁ K₂ H w₁ w₂) : T2Four1 C₁ z u K₂ K₁ H w₂ w₁ where
  zz := h.zz
  z_ne := h.z_ne
  uu := h.uu
  u_ne := h.u_ne
  zu_ne := h.zu_ne
  zu_comm := h.zu_comm
  K_comm := fun x hx y hy => (h.K_comm y hy x hx).symm
  K_inter := by rw [inf_comm]; exact h.K_inter
  C_comm := h.C_comm
  K_le_C := by rw [sup_comm]; exact h.K_le_C
  C_norm₁ := h.C_norm₂
  C_norm₂ := h.C_norm₁
  C_idx := by rw [sup_comm]; exact h.C_idx
  H_comm := h.H_comm
  z_mem_H := h.z_mem_H
  u_mem_H := h.u_mem_H
  H_le_C := h.H_le_C
  H_not_le_K := by rw [sup_comm]; exact h.H_not_le_K
  H₁_iff := h.H₂_iff
  H₂_iff := h.H₁_iff
  w₁_mem := h.w₂_mem
  w₂_mem := h.w₁_mem
  w₁_sq := h.w₂_sq
  w₂_sq := h.w₁_sq
  w₁_u := h.w₂_u
  w₂_u := h.w₁_u
  w₁_normH := h.w₂_normH
  w₂_normH := h.w₁_normH
  w₀_inv := by rw [← h.w₁w₂_comm]; exact h.w₀_inv
  w₀_not_mem := by rw [← h.w₁w₂_comm]; exact h.w₀_not_mem

theorem Ch6NegCfg.swap {q : ℕ} (h : Ch6NegCfg C₁ q z u K₁ K₂ H w₁ w₂) :
    Ch6NegCfg C₁ q z u K₂ K₁ H w₂ w₁ where
  toT2Four1 := h.toT2Four1.swap
  H₁_cyc := h.H₂_cyc
  H₂_cyc := h.H₁_cyc
  H₁_card := h.H₂_card
  H₂_card := h.H₁_card
  H_idx := by rw [sup_comm]; exact h.H_idx
  H₁_cent := h.H₂_cent
  H₂_cent := h.H₁_cent

end CFSG.GH74.GLS.Stage4.Rest
