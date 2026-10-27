module

public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecCtx
public import CFSG.GH74.GLS.Stage4.T2NumGtMixSecDefs
public import CFSG.GH74.GLS.Stage4.T2Omega1
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T2P53e

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem ch6Mix_weyl : Ch6MixWeyl := by
  intro G _ _ hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem hlt hmod N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord
    N2 hN2 hF
  subst hN2
  suffices h : ∃ a : G, a⁻¹ * N2.z * a = u ∧ Ch6Weyl (⟨N2, a⟩ : T2N3 G) by
    obtain ⟨a, ha, hW⟩ := h
    exact ⟨⟨N2, a⟩, rfl, hW, ha⟩
  have hLocW : Ch6Loc5W N2.toT2N1 u := hLoc.toCh6Loc5W
  have ctx := t2Ctx_ofW hSet hRem hLocW hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨hw₀sq, hw₀H, hY1⟩ := t2MixSec_Y1 hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  subst hz hK₁ hK₂ hq₁ hq₂
  have hz2 : N2.z * N2.z = 1 := ctx.zz
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hzu : N2.z * u = u * N2.z := hLoc.u_comm.symm
  have hzne : N2.z ≠ u := hLoc.u_ne.symm
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hw₁z : N2.w₁ * N2.z = N2.z * N2.w₁ := hLoc.z_cent_S N2.w₁ hLoc.w₁_memS
  have hw₂z : N2.w₂ * N2.z = N2.z * N2.w₂ := hLoc.z_cent_S N2.w₂ hLoc.w₂_memS
  have hw₁w₂ : N2.w₁ * N2.w₂ = N2.w₂ * N2.w₁ := hSet.comm _ hLoc.w₁_mem _ hLoc.w₂_mem
  have hw₁H : ∀ h ∈ N2.H, N2.w₁ * h * N2.w₁⁻¹ ∈ N2.H :=
    fun h hh => (Subgroup.mem_normalizer_iff.1 hLoc.w₁_normH h).1 hh
  have hw₂H : ∀ h ∈ N2.H, N2.w₂ * h * N2.w₂⁻¹ ∈ N2.H :=
    fun h hh => (Subgroup.mem_normalizer_iff.1 hLoc.w₂_normH h).1 hh
  have hΩ := t2_omega1_zu hr hLoc.H_comm hLoc.z_mem_H hLoc.u_mem_H hz2 hu2 ctx.z_ne hu1 hzne
    hw₀sq hw₀H hLoc.w₀_inv
  have hFS : ∀ f ∈ N2.F, ∀ s ∈ N2.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N2.S : Set G) := by
      rw [hF.centS]; exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hFodd : ∀ f ∈ N2.F, Odd (orderOf f) := hF.F_odd
  have hFw₁ : ∀ f ∈ N2.F, f * N2.w₁ = N2.w₁ * f := fun f hf => hFS f hf _ hLoc.w₁_memS
  have hFw₂ : ∀ f ∈ N2.F, f * N2.w₂ = N2.w₂ * f := fun f hf => hFS f hf _ hLoc.w₂_memS
  have hFu : ∀ f ∈ N2.F, f * u = u * f := fun f hf => hFS f hf u hLoc.u_mem_S
  have hFz : ∀ f ∈ N2.F, f * N2.z = N2.z * f := fun f hf => hFS f hf _ hLoc.z_mem_S
  have hFH : ∀ f ∈ N2.F, ∀ h ∈ N2.H, f * h * f⁻¹ ∈ N2.H :=
    fun f hf h hh => (Subgroup.mem_normalizer_iff.1 (hF.F_normH hf) h).1 hh
  have hFn := t2P53_F_normC₁ ctx hFz
  have hY1' : ∀ c ∈ N2.K₁ ⊔ N2.K₂ ⊔ N2.S, c * u = u * c →
      c ∈ N2.H ∨ ∃ h ∈ N2.H, c = h * (N2.w₁ * N2.w₂) := fun c hc =>
    hY1 c (by rw [← ctx.KS]; exact hc)
  have hdec : ∀ y : G, y * N2.z = N2.z * y → y * u = u * y →
      ∃ k f : G, f ∈ N2.F ∧ (k ∈ N2.H ∨ ∃ h ∈ N2.H, k = h * (N2.w₁ * N2.w₂)) ∧ y = k * f :=
    fun y hyz hyu => t2Y_decomp hF.C_le hFn hFu hY1' hyz hyu
  obtain ⟨c, hc⟩ := isConj_iff.1 (hLoc.one_class u hLoc.u_ord)
  have hg : c⁻¹⁻¹ * N2.z * c⁻¹ = u := by simpa using hc
  have hK₁inv := t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  have hK₂inv := t2P53_invK hodd₂ e₂ hSet.z_mem₂ hze₂
  have hnc := t2P53_hnc hSet hRem ctx hF.C_le hFodd hFz hF.F_inter_K hK₂inv hg hzu hzne
  have hnorm : ∀ c' : G, c' * N2.z = N2.z * c' → ∀ x ∈ N2.K₁, c' * x * c'⁻¹ ∈ N2.K₁ :=
    fun c' hc' => (t2P53_Cnorm hSet hRem ctx hF.C_le hFodd hFz hc').1
  obtain ⟨v, hvv, hvz⟩ := t2P53_v hodd₁ h3₁ e₁ hz2 hzu hg hnorm hK₁inv hnc
  obtain ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a, haNsub, hFN⟩ :=
    t2P53_core (w₀ := N2.w₁ * N2.w₂) rfl hz2 hu2 hzu hw₁z hLoc.w₁_u hLoc.w₁_sq hw₂z hLoc.w₂_u hw₁w₂
      hvv hvz hLoc.H_comm hLoc.z_mem_H hLoc.u_mem_H hw₁H hw₂H hw₀sq hw₀H hLoc.w₀_inv hΩ hFodd hFw₁
      hFw₂ hFu hFz hFH hdec
  refine ⟨a, d1, ?_⟩
  exact
    { a_normH := haN
      a_cube := ha3
      w₁_a := hw₁a
      w₂_a := hw₂a
      a_mem_N := haNsub
      a_cycle := by
        show a⁻¹ * (a⁻¹ * N2.z * a) * a = N2.z * (a⁻¹ * N2.z * a)
        rw [d1]; exact d2
      F_normN := fun f hf => hFN f hf }

end CFSG.GH74.GLS.Stage4.Rest
