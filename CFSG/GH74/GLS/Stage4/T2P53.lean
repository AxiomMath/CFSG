module

public import CFSG.GH74.GLS.Stage4.T2P53e
public import CFSG.GH74.GLS.Stage4.T2Omega1
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T2Steps

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

theorem ch6T2P53 : Ch6T2P53 := by
  intro G _ _ hr Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord hF
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  obtain ⟨hw₀sq, hw₀H, hY1⟩ := t2Ctx_Y1 hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  subst hz hK₁ hK₂ hq₁ hq₂
  have hz2 : N.z * N.z = 1 := ctx.zz
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hLoc.u_ord, sq] at h
    exact h
  have hzu : N.z * u = u * N.z := hLoc.u_comm.symm
  have hzne : N.z ≠ u := hLoc.u_ne.symm
  have hu1 : u ≠ 1 := by
    intro h
    have := hLoc.u_ord
    rw [h, orderOf_one] at this
    omega
  have hw₁z : N.w₁ * N.z = N.z * N.w₁ := hLoc.z_cent_S N.w₁ hLoc.w₁_memS
  have hw₂z : N.w₂ * N.z = N.z * N.w₂ := hLoc.z_cent_S N.w₂ hLoc.w₂_memS
  have hw₁w₂ : N.w₁ * N.w₂ = N.w₂ * N.w₁ := hSet.comm _ hLoc.w₁_mem _ hLoc.w₂_mem
  have hw₁H : ∀ h ∈ N.H, N.w₁ * h * N.w₁⁻¹ ∈ N.H :=
    fun h hh => (Subgroup.mem_normalizer_iff.1 hLoc.w₁_normH h).1 hh
  have hw₂H : ∀ h ∈ N.H, N.w₂ * h * N.w₂⁻¹ ∈ N.H :=
    fun h hh => (Subgroup.mem_normalizer_iff.1 hLoc.w₂_normH h).1 hh
  have hΩ := t2_omega1_zu hr hLoc.H_comm hLoc.z_mem_H hLoc.u_mem_H hz2 hu2 ctx.z_ne hu1 hzne
    hw₀sq hw₀H hLoc.w₀_inv
  have hFS : ∀ f ∈ N.F, ∀ s ∈ N.S, f * s = s * f := by
    intro f hf s hs
    have hfC : f ∈ centralizer (N.S : Set G) := by
      rw [hF.centS]; exact Subgroup.mem_sup_right hf
    exact (Subgroup.mem_centralizer_iff.1 hfC s hs).symm
  have hFodd : ∀ f ∈ N.F, Odd (orderOf f) := hF.F_odd
  have hFw₁ : ∀ f ∈ N.F, f * N.w₁ = N.w₁ * f := fun f hf => hFS f hf _ hLoc.w₁_memS
  have hFw₂ : ∀ f ∈ N.F, f * N.w₂ = N.w₂ * f := fun f hf => hFS f hf _ hLoc.w₂_memS
  have hFu : ∀ f ∈ N.F, f * u = u * f := fun f hf => hFS f hf u hLoc.u_mem_S
  have hFz : ∀ f ∈ N.F, f * N.z = N.z * f := fun f hf => hFS f hf _ hLoc.z_mem_S
  have hFH : ∀ f ∈ N.F, ∀ h ∈ N.H, f * h * f⁻¹ ∈ N.H :=
    fun f hf h hh => (Subgroup.mem_normalizer_iff.1 (hF.F_normH hf) h).1 hh
  have hFn := t2P53_F_normC₁ ctx hFz
  have hY1' : ∀ c ∈ N.K₁ ⊔ N.K₂ ⊔ N.S, c * u = u * c →
      c ∈ N.H ∨ ∃ h ∈ N.H, c = h * (N.w₁ * N.w₂) := fun c hc =>
    hY1 c (by rw [← ctx.KS]; exact hc)
  have hdec : ∀ y : G, y * N.z = N.z * y → y * u = u * y →
      ∃ k f : G, f ∈ N.F ∧ (k ∈ N.H ∨ ∃ h ∈ N.H, k = h * (N.w₁ * N.w₂)) ∧ y = k * f :=
    fun y hyz hyu => t2Y_decomp hF.C_le hFn hFu hY1' hyz hyu
  obtain ⟨c, hc⟩ := isConj_iff.1 (hLoc.one_class u hLoc.u_ord)
  have hg : c⁻¹⁻¹ * N.z * c⁻¹ = u := by simpa using hc
  have hK₁inv := t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  have hK₂inv := t2P53_invK hodd₂ e₂ hSet.z_mem₂ hze₂
  have hnc := t2P53_hnc hSet hRem ctx hF.C_le hFodd hFz hF.F_inter_K hK₂inv hg hzu hzne
  have hnorm : ∀ c' : G, c' * N.z = N.z * c' → ∀ x ∈ N.K₁, c' * x * c'⁻¹ ∈ N.K₁ :=
    fun c' hc' => (t2P53_Cnorm hSet hRem ctx hF.C_le hFodd hFz hc').1
  obtain ⟨v, hvv, hvz⟩ := t2P53_v hodd₁ h3₁ e₁ hz2 hzu hg hnorm hK₁inv hnc
  obtain ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a, haNsub, hFN⟩ :=
    t2P53_core (w₀ := N.w₁ * N.w₂) rfl hz2 hu2 hzu hw₁z hLoc.w₁_u hLoc.w₁_sq hw₂z hLoc.w₂_u hw₁w₂
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
        show a⁻¹ * (a⁻¹ * N.z * a) * a = N.z * (a⁻¹ * N.z * a)
        rw [d1]; exact d2
      F_normN := fun f hf => hFN f hf }

end CFSG.GH74.GLS.Stage4.Rest
