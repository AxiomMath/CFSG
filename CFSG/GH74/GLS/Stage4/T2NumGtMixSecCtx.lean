module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixCtx

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem t2MixSec_Y1
    {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5M N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) :
    (N.w₁ * N.w₂) * (N.w₁ * N.w₂) = 1 ∧ (N.w₁ * N.w₂) ∉ N.H ∧
      ∀ y ∈ oPrimeResidualOf 2 (centralizer ({N.z} : Set G)), y * u = u * y →
        y ∈ N.H ∨ ∃ h ∈ N.H, y = h * (N.w₁ * N.w₂) := by
  have ctx := t2Ctx_ofW hSet hRem hLoc.toCh6Loc5W hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨q₁, q₂, z, S, K₁, K₂, H, X₁, X₁', X₂, X₂', w₁, w₂⟩ := N
  have hww : w₁ * w₂ = w₂ * w₁ := hSet.comm w₁ hLoc.w₁_mem w₂ hLoc.w₂_mem
  have hw₀sq : (w₁ * w₂) * (w₁ * w₂) = 1 := by
    calc (w₁ * w₂) * (w₁ * w₂) = w₁ * (w₂ * w₁) * w₂ := by group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [← hww]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hLoc.w₁_sq, hLoc.w₂_sq, ctx.zz]
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hHiff : ∀ (K : Subgroup G), H ⊓ K = centralizer ({u} : Set G) ⊓ K →
      ∀ x ∈ K, x ∈ H ↔ x * u = u * x := by
    intro K h x hx
    constructor
    · intro hxH
      have : x ∈ H ⊓ K := ⟨hxH, hx⟩
      rw [h] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this.1
    · intro hxu
      have : x ∈ centralizer ({u} : Set G) ⊓ K :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hxu, hx⟩
      rw [← h] at this
      exact this.1
  have hH₁ : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x := hHiff K₁ hLoc.H₁_eq
  have hH₂ : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x := hHiff K₂ hLoc.H₂_eq
  have hHC : H ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← ctx.KS]; exact hLoc.H_le
  have hzc : ∀ x ∈ oPrimeResidualOf 2 (centralizer ({z} : Set G)), x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (ctx.C₁C hx)
  have hKC : K₁ ⊔ K₂ ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := hSet.le_residual
  obtain ⟨hn₁, hn₂⟩ := t2C_C₁_normalizes hRem hSet.comm
  obtain ⟨s₀, hs₀H, hs₀K⟩ := IsConcreteLE.not_le_iff_exists.1 hLoc.H_not_le_K
  have hY1 := t2C_Y1 hSet.comm hSet.inter_eq.le ctx.zz hzc hKC (ctx.SC₁ hLoc.u_mem_S) hn₁ hn₂ hu2
    hLoc.w₁_mem hLoc.w₂_mem hLoc.w₁_u hLoc.w₂_u hH₁ hH₂ hLoc.H_comm hLoc.u_mem_H hHC
    hLoc.w₀_inv hSet.index_two hs₀H hs₀K
  have hcardH₁ : 3 ≤ Nat.card ↥(H ⊓ K₁) := by
    have h1 : Nat.card ↥(H ⊓ K₁) = q₁ + 1 := hLoc.card_H_K₁
    have h2 : 5 ≤ q₁ := hLoc.q₁_ge
    omega
  exact ⟨hw₀sq, t2C_w0_not_mem hLoc.H_comm hLoc.w₀_inv hLoc.H₁_cyc hcardH₁, hY1⟩

theorem t2MixSec_normH
    {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ} {z t : G}
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (hSet : Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂) (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) {N : T2N1 G} {u : G}
    (hLoc : Ch6Loc5M N u) (hz : N.z = z) (hK₁ : N.K₁ = K₁) (hK₂ : N.K₂ = K₂) (hq₁ : N.q₁ = q₁)
    (hq₂ : N.q₂ = q₂) {f : G} (hodd : Odd (orderOf f)) (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∀ h ∈ N.H, f * h * f⁻¹ ∈ N.H := by
  have ctx := t2Ctx_ofW hSet hRem hLoc.toCh6Loc5W hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨hw₀sq, hw₀H, hY1⟩ := t2MixSec_Y1 hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨q₁, q₂, z, S, K₁, K₂, H, X₁, X₁', X₂, X₂', w₁, w₂⟩ := N
  have hHiff : ∀ (K : Subgroup G), H ⊓ K = centralizer ({u} : Set G) ⊓ K →
      ∀ x ∈ K, x ∈ H ↔ x * u = u * x := by
    intro K h x hx
    constructor
    · intro hxH
      have : x ∈ H ⊓ K := ⟨hxH, hx⟩
      rw [h] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this.1
    · intro hxu
      have : x ∈ centralizer ({u} : Set G) ⊓ K :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hxu, hx⟩
      rw [← h] at this
      exact this.1
  have hH₁ : ∀ x ∈ K₁, x ∈ H ↔ x * u = u * x := hHiff K₁ hLoc.H₁_eq
  have hH₂ : ∀ x ∈ K₂, x ∈ H ↔ x * u = u * x := hHiff K₂ hLoc.H₂_eq
  have hHC : H ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [← ctx.KS]; exact hLoc.H_le
  have hfz : f * z = z * f := hfS z hLoc.z_mem_S
  have hfC' : f ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hfz
  obtain ⟨hfn₁, hfn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
  intro h hh
  exact t2C_normH hY1 hHC hLoc.u_mem_H hLoc.H_comm hH₁ hH₂ hSet.comm hw₀sq hw₀H
    hLoc.H_idx (fun x hx => ctx.C₁norm f hfC' x hx) hfn₁ hfn₂ (hfS u hLoc.u_mem_S)
    (hfS (w₁ * w₂) (Subgroup.mul_mem _ hLoc.w₁_memS hLoc.w₂_memS)) hodd h hh

end CFSG.GH74.GLS.Stage4.Rest
