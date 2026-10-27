module

public import CFSG.GH74.GLS.Stage4.T2NegFour
public import CFSG.GH74.GLS.Stage4.T2P53a
public import CFSG.GH74.GLS.Stage4.T2P53e

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2

section Weyl

variable {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q : ℕ} {z t : G}
  {K₁ K₂ S : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem exists_a_neg (hr : pRank 2 G = 3) (hSet : Ch6Setup G Gs q q z K₁ K₂ F₁ F₂)
    (hRem : Ch6Rem z K₁ K₂ F₁ F₂ t) (ctx : T2Ctx z K₁ K₂ S) {F : Subgroup G}
    (hCle : centralizer ({z} : Set G) ≤ K₁ ⊔ K₂ ⊔ S ⊔ F) (hFodd : ∀ f ∈ F, Odd (orderOf f))
    (hFS : ∀ f ∈ F, ∀ s ∈ S, f * s = s * f) (hFK : F ⊓ (K₁ ⊔ K₂) = ⊥)
    {u : G} {H : Subgroup G} {w₁ w₂ : G}
    (cfg : Ch6NegCfg (oPrimeResidualOf 2 (centralizer ({z} : Set G))) q z u K₁ K₂ H w₁ w₂)
    (huS : u ∈ S) (hw₁S : w₁ ∈ S) (hw₂S : w₂ ∈ S) :
    ∃ a : G, a⁻¹ * z * a = u ∧ a⁻¹ * u * a = z * u ∧ a ∈ normalizer (H : Set G) ∧ a ^ 3 ∈ H ∧
      (∃ h ∈ H, w₁ * a * w₁⁻¹ = a⁻¹ * h) ∧ (∃ h ∈ H, w₂ * a * w₂⁻¹ = a⁻¹ * h) := by
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hodd₁ : Odd (Nat.card F₁) := by rw [hSet.card₁]; exact hSet.odd₁
  have hodd₂ : Odd (Nat.card F₂) := by rw [hSet.card₂]; exact hSet.odd₂
  have h3₁ : 3 < Nat.card F₁ := by rw [hSet.card₁]; have := hSet.five; omega
  have hz2 : z * z = 1 := cfg.zz
  have hu2 : u * u = 1 := cfg.uu
  have hzu : z * u = u * z := cfg.zu_comm
  have hzne : z ≠ u := cfg.zu_ne
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) cfg.u_ne
  have hw₁z : w₁ * z = z * w₁ := cfg.w₁_z
  have hw₂z : w₂ * z = z * w₂ := cfg.w₂_z
  have hw₁w₂ : w₁ * w₂ = w₂ * w₁ := cfg.w₁w₂_comm
  have hw₁H : ∀ h ∈ H, w₁ * h * w₁⁻¹ ∈ H := cfg.w₁_normH
  have hw₂H : ∀ h ∈ H, w₂ * h * w₂⁻¹ ∈ H := cfg.w₂_normH
  have hw₀sq : (w₁ * w₂) * (w₁ * w₂) = 1 := cfg.w₀_sq
  have hw₀H : (w₁ * w₂) ∉ H := cfg.w₀_not_mem
  have hΩ := cfg.omega1 hr
  have hFz : ∀ f ∈ F, f * z = z * f := fun f hf => hFS f hf z ctx.Sctx.zS
  have hFw₁ : ∀ f ∈ F, f * w₁ = w₁ * f := fun f hf => hFS f hf _ hw₁S
  have hFw₂ : ∀ f ∈ F, f * w₂ = w₂ * f := fun f hf => hFS f hf _ hw₂S
  have hFu : ∀ f ∈ F, f * u = u * f := fun f hf => hFS f hf u huS
  have hFn := t2P53_F_normC₁ ctx hFz
  have hY1' : ∀ c ∈ K₁ ⊔ K₂ ⊔ S, c * u = u * c →
      c ∈ H ∨ ∃ h ∈ H, c = h * (w₁ * w₂) := fun c hc =>
    cfg.Y1 c (by rw [← ctx.KS]; exact hc)
  have hFH : ∀ f ∈ F, ∀ h ∈ H, f * h * f⁻¹ ∈ H := by
    intro f hf
    obtain ⟨hfn₁, hfn₂⟩ := t2Ctx_odd_normK ctx (hFz f hf) (hFodd f hf)
    exact t2C_normH (C₁ := oPrimeResidualOf 2 (centralizer ({z} : Set G))) cfg.Y1 cfg.H_le_C
      cfg.u_mem_H cfg.H_comm cfg.H₁_iff cfg.H₂_iff cfg.K_comm hw₀sq hw₀H cfg.H_idx
      (fun x hx => ctx.C₁norm f (Subgroup.mem_centralizer_singleton_iff.2 (hFz f hf)) x hx)
      hfn₁ hfn₂ (hFu f hf)
      (hFS f hf (w₁ * w₂) (Subgroup.mul_mem _ hw₁S hw₂S)) (hFodd f hf)
  have hdec : ∀ y : G, y * z = z * y → y * u = u * y →
      ∃ k f : G, f ∈ F ∧ (k ∈ H ∨ ∃ h ∈ H, k = h * (w₁ * w₂)) ∧ y = k * f :=
    fun y hyz hyu => t2Y_decomp hCle hFn hFu hY1' hyz hyu
  obtain ⟨c, hc⟩ := isConj_iff.1 (hSet.one_class u hu_ord)
  have hg : c⁻¹⁻¹ * z * c⁻¹ = u := by simpa using hc
  have hK₁inv := t2P53_invK hodd₁ e₁ hSet.z_mem₁ hze₁
  have hK₂inv := t2P53_invK hodd₂ e₂ hSet.z_mem₂ hze₂
  have hnc := t2P53_hnc hSet hRem ctx hCle hFodd hFz hFK hK₂inv hg hzu hzne
  have hnorm : ∀ c' : G, c' * z = z * c' → ∀ x ∈ K₁, c' * x * c'⁻¹ ∈ K₁ :=
    fun c' hc' => (t2P53_Cnorm hSet hRem ctx hCle hFodd hFz hc').1
  obtain ⟨v, hvv, hvz⟩ := t2P53_v hodd₁ h3₁ e₁ hz2 hzu hg hnorm hK₁inv hnc
  obtain ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a, -, -⟩ :=
    t2P53_core (w₀ := w₁ * w₂) rfl hz2 hu2 hzu hw₁z cfg.w₁_u cfg.w₁_sq hw₂z cfg.w₂_u hw₁w₂
      hvv hvz cfg.H_comm cfg.z_mem_H cfg.u_mem_H hw₁H hw₂H hw₀sq hw₀H cfg.w₀_inv hΩ hFodd hFw₁
      hFw₂ hFu hFz hFH hdec
  exact ⟨a, d1, d2, haN, ha3, hw₁a, hw₂a⟩

end Weyl

end CFSG.GH74.GLS.Stage4.Rest
