module

public import CFSG.ClassicalInvolution.Phan.PhanQ57RatSetup

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Side

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem side_inf {W₀ : Submodule K (V8 K)} (hW : PhanSolid D W₀) {x y r₁ c e : V8 K}
    (hx : x ∈ W₀) (hy : y ∈ W₀) (hr₁ : r₁ ∈ W₀)
    (hind : ∀ s t δ : K, s • x + t • y + δ • r₁ = 0 → s = 0 ∧ t = 0 ∧ δ = 0)
    {ξ β ξ' β' γ f : K} (hf : D.τ f = f) (hβ' : β' ≠ 0)
    (hN : (β' * γ - β * f) * D.τ (β' * γ - β * f) ≠ (β' * γ) * D.τ (β' * γ))
    (hc : c = ξ • x + β • y + γ • (r₁ + conj D r₁)) (he : e = ξ' • x + β' • y + f • r₁)
    {v : V8 K} (hv : v ∈ Submodule.span K {x, c, e})
    (hcv : conj D v ∈ Submodule.span K {x, c, e}) : v = 0 := by
  obtain ⟨s, t, u, hvs⟩ := mem_span_triple' hv
  obtain ⟨s', t', u', hvs'⟩ := mem_span_triple' hcv
  have e1 : s' • x + t' • c + u' • e = conj D (s • x + t • c + u • e) := by
    rw [← hvs, hvs']
  subst hc he
  have hw₂W : (s + t * ξ + u * ξ') • x + (t * β + u * β') • y +
      (t * γ + u * f - D.τ (t' * γ)) • r₁ ∈ W₀ :=
    W₀.add_mem (W₀.add_mem (W₀.smul_mem _ hx) (W₀.smul_mem _ hy)) (W₀.smul_mem _ hr₁)
  have hw₁W : (s' + t' * ξ + u' * ξ') • x + (t' * β + u' * β') • y +
      (t' * γ + u' * f - D.τ (t * γ)) • r₁ ∈ W₀ :=
    W₀.add_mem (W₀.add_mem (W₀.smul_mem _ hx) (W₀.smul_mem _ hy)) (W₀.smul_mem _ hr₁)
  have key : (s' + t' * ξ + u' * ξ') • x + (t' * β + u' * β') • y +
      (t' * γ + u' * f - D.τ (t * γ)) • r₁ =
      conj D ((s + t * ξ + u * ξ') • x + (t * β + u * β') • y +
        (t * γ + u * f - D.τ (t' * γ)) • r₁) := by
    simp only [conj_add, conj_smul, conj_conj, map_add, map_mul, map_sub, D.tau_tau, hf] at e1 ⊢
    linear_combination (norm := module) e1
  have hw₂0 := hW.inf _ hw₂W (by rw [← key]; exact hw₁W)
  have hw₁0 : (s' + t' * ξ + u' * ξ') • x + (t' * β + u' * β') • y +
      (t' * γ + u' * f - D.τ (t * γ)) • r₁ = 0 := by
    rw [key, hw₂0]
    exact conj_zero' D
  obtain ⟨hpx, hpy, hpr⟩ := hind _ _ _ hw₂0
  obtain ⟨hpx', hpy', hpr'⟩ := hind _ _ _ hw₁0
  have E3 : t * γ + u * f = D.τ (t' * γ) := by linear_combination hpr
  have E4 : t' * γ + u' * f = D.τ (t * γ) := by linear_combination hpr'
  have E3' : t * (β' * γ - β * f) = β' * D.τ (t' * γ) := by
    linear_combination β' * E3 - f * hpy
  have E4' : t' * (β' * γ - β * f) = β' * D.τ (t * γ) := by
    linear_combination β' * E4 - f * hpy'
  have E4'' := congrArg D.τ E4'
  simp only [map_mul, map_sub, D.tau_tau, hf] at E4'' E3'
  have key2 : t * ((β' * γ - β * f) * D.τ (β' * γ - β * f) - (β' * γ) * D.τ (β' * γ)) = 0 := by
    simp only [map_mul, map_sub, hf]
    linear_combination (D.τ β' * D.τ γ - D.τ β * f) * E3' + (β' * D.τ γ) * E4''
  have ht0 : t = 0 := (mul_eq_zero.1 key2).resolve_right (sub_ne_zero.2 hN)
  have hu0 : u = 0 := by
    rw [ht0, zero_mul, zero_add] at hpy
    exact (mul_eq_zero.1 hpy).resolve_right hβ'
  have hs0 : s = 0 := by
    rw [ht0, hu0, zero_mul, zero_mul, add_zero, add_zero] at hpx
    exact hpx
  rw [hvs, ht0, hu0, hs0]
  simp

theorem side_solid [Finite F] [Finite K] (hodd : Odd (Nat.card F)) (h2 : (2 : K) ≠ 0)
    (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) {W₀ : Submodule K (V8 K)}
    (hW : PhanSolid D W₀) {x y r₁ c e : V8 K} (hx : x ∈ W₀) (hy : y ∈ W₀) (hr₁ : r₁ ∈ W₀)
    (hr₁0 : r₁ ≠ 0) (hxy : ColK D x y) (hxr : her D r₁ x = 0) (hyr : her D r₁ y = 0)
    {ξ β ξ' β' γ f : K} (hf : D.τ f = f) (hβ' : β' ≠ 0)
    (hN : (β' * γ - β * f) * D.τ (β' * γ - β * f) ≠ (β' * γ) * D.τ (β' * γ))
    (hc : c = ξ • x + β • y + γ • (r₁ + conj D r₁)) (he : e = ξ' • x + β' • y + f • r₁)
    (hQx : Q8 x = 0) (hQc : Q8 c = 0) (hQe : Q8 e = 0) (hxc : ColK D x c) (hxe : B8 x e = 0)
    (hce : B8 c e = 0) : ∃ W, PhanSolid D W ∧ x ∈ W ∧ c ∈ W ∧ e ∈ W := by
  have hts := ts_triple hQx hQc hQe hxc.1 hxe hce
  have hind : ∀ s t δ : K, s • x + t • y + δ • r₁ = 0 → s = 0 ∧ t = 0 ∧ δ = 0 :=
    fun s t δ h => hxy.indep_rad D hr₁0 hxr hyr h
  have hxPl : x ∈ Submodule.span K {x, c, e} := Submodule.subset_span (by simp)
  have hcPl : c ∈ Submodule.span K {x, c, e} := Submodule.subset_span (by simp)
  have hePl : e ∈ Submodule.span K {x, c, e} := Submodule.subset_span (by simp)
  obtain ⟨W, hWp, hPlW⟩ := exists_phanSolid_of_colK D hodd h2 hε hσ hts
    (finrank_span_three_le x c e)
    (fun v hv hcv => side_inf D hW hx hy hr₁ hind hf hβ' hN hc he hv hcv) hxPl hcPl hxc
  exact ⟨W, hWp, hPlW hxPl, hPlW hcPl, hPlW hePl⟩

end Side

end CFSG.ClassicalInvolution.PhanQ
