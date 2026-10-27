module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixCtx
public import CFSG.GH74.GLS.Stage4.T2NumGtMixLocDefs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Conv

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
  {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem Ch6Loc5M.toMixCfg
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5M N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) :
    Ch6MixCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q₁ q₂ z u K₁ K₂ N.H N.w₁ N.w₂ := by
  have ctx := t2Ctx_ofW hSet hRem hLoc.toCh6Loc5W hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have hzz : N.z * N.z = 1 := t2C_zz hSet
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hHiff : ∀ (K : Subgroup G), N.H ⊓ K = centralizer ({u} : Set G) ⊓ K →
      ∀ x ∈ K, x ∈ N.H ↔ x * u = u * x := by
    intro K h x hx
    constructor
    · intro hxH
      have : x ∈ N.H ⊓ K := ⟨hxH, hx⟩
      rw [h] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this.1
    · intro hxu
      have : x ∈ centralizer ({u} : Set G) ⊓ K :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hxu, hx⟩
      rw [← h] at this
      exact this.1
  have hHC : N.H ≤ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)) := by
    rw [← ctx.KS]; exact hLoc.H_le
  have hcardH₁ : 3 ≤ Nat.card ↥(N.H ⊓ N.K₁) := by
    have h1 : Nat.card ↥(N.H ⊓ N.K₁) = N.q₁ + 1 := hLoc.card_H_K₁
    have h2 : 5 ≤ N.q₁ := hLoc.q₁_ge
    omega
  refine
    { zz := hzz, z_ne := t2C_z_ne hSet, uu := hu2, u_ne := hu1, zu_ne := hLoc.u_ne.symm,
      zu_comm := hLoc.u_comm.symm, K_comm := hSet.comm, K_inter := hSet.inter_eq.le,
      C_comm := fun x hx => Subgroup.mem_centralizer_singleton_iff.1 (ctx.C₁C hx),
      K_le_C := hSet.le_residual,
      C_norm₁ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).1 c hc,
      C_norm₂ := fun c hc => (t2C_C₁_normalizes hRem hSet.comm).2 c hc,
      C_idx := hSet.index_two,
      H_comm := hLoc.H_comm, z_mem_H := hLoc.z_mem_H, u_mem_H := hLoc.u_mem_H, H_le_C := hHC,
      H_not_le_K := hLoc.H_not_le_K, H₁_iff := hHiff _ hLoc.H₁_eq, H₂_iff := hHiff _ hLoc.H₂_eq,
      w₁_mem := hLoc.w₁_mem, w₂_mem := hLoc.w₂_mem, w₁_sq := hLoc.w₁_sq, w₂_sq := hLoc.w₂_sq,
      w₁_u := hLoc.w₁_u, w₂_u := hLoc.w₂_u,
      w₁_normH := fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₁_normH x).1 hx,
      w₂_normH := fun x hx => (Subgroup.mem_normalizer_iff.1 hLoc.w₂_normH x).1 hx,
      w₀_inv := hLoc.w₀_inv,
      w₀_not_mem := t2C_w0_not_mem hLoc.H_comm hLoc.w₀_inv hLoc.H₁_cyc hcardH₁,
      H₁_cyc := hLoc.H₁_cyc, H₂_cyc := hLoc.H₂_cyc, H₁_card := hLoc.card_H_K₁,
      H₂_card := hLoc.card_H_K₂, H_idx := hLoc.H_idx, H₁_cent := hLoc.H₁_cent }

end Conv

end CFSG.GH74.GLS.Stage4.Rest
