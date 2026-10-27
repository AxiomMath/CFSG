module

public import CFSG.GroupTheory.ABGLocalTools.OddInvolution

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

theorem t6_inv_mod {R X : Subgroup G} (hXc : ∀ x ∈ X, ∀ r ∈ R, x * r = r * x)
    (hodd : Odd (Nat.card R)) {z : G} (hz2 : orderOf z = 2) (hzR : z ∈ normalizer (R : Set G))
    (hfix : ∀ r ∈ R, z * r * z⁻¹ = r → r ∈ X) :
    (∀ r ∈ R, z * r * z⁻¹ * r ∈ X) ∧ ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X := by
  obtain ⟨hdec, -⟩ := CFSG.ABGLocalTools.odd_fixed_mul_inverted hodd hz2 hzR
  have hinv : ∀ r ∈ R, z * r * z⁻¹ * r ∈ X := by
    intro r hr
    have hr' : r ∈ (R : Set G) := hr
    rw [hdec] at hr'
    obtain ⟨c, hc, i, hi, rfl⟩ := hr'
    have hcR : c ∈ R := hc.1
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc.2
    have hcz' : z * c * z⁻¹ = c := by rw [← hcz]; group
    have hcX : c ∈ X := hfix c hcR hcz'
    have hiR : i ∈ R := hi.1
    have hiz : z * i * z⁻¹ = i⁻¹ := hi.2
    have e1 : z * (c * i) * z⁻¹ * (c * i) = c * (i⁻¹ * c) * i := by
      calc z * (c * i) * z⁻¹ * (c * i) = (z * c * z⁻¹) * (z * i * z⁻¹) * (c * i) := by group
        _ = c * i⁻¹ * (c * i) := by rw [hcz', hiz]
        _ = c * (i⁻¹ * c) * i := by group
    rw [e1, ← hXc c hcX i⁻¹ (R.inv_mem hiR)]
    have : c * (c * i⁻¹) * i = c * c := by group
    rw [this]
    exact X.mul_mem hcX hcX
  refine ⟨hinv, fun r hr s hs => ?_⟩
  have key : ∀ r ∈ R, ∀ s ∈ R, r⁻¹ * s⁻¹ * r * s ∈ X := by
    intro r hr s hs
    have hx₁ := hinv r hr
    have hx₂ := hinv s hs
    have hx₃ := hinv (r * s) (R.mul_mem hr hs)
    set x₁ := z * r * z⁻¹ * r with hx₁def
    set x₂ := z * s * z⁻¹ * s with hx₂def
    set x₃ := z * (r * s) * z⁻¹ * (r * s) with hx₃def
    have hr1 : z * r * z⁻¹ = x₁ * r⁻¹ := by rw [hx₁def]; group
    have hs1 : z * s * z⁻¹ = x₂ * s⁻¹ := by rw [hx₂def]; group
    have h1 : z * (r * s) * z⁻¹ = (x₁ * r⁻¹) * (x₂ * s⁻¹) := by
      rw [← hr1, ← hs1]; group
    have h2 : z * (r * s) * z⁻¹ = x₃ * (s⁻¹ * r⁻¹) := by rw [hx₃def]; group
    have h3 : x₃ = (x₁ * r⁻¹) * (x₂ * s⁻¹) * (r * s) := by
      have : x₃ * (s⁻¹ * r⁻¹) * (r * s) = x₃ := by group
      rw [← this, ← h2, h1]
    have h4 : r⁻¹ * x₂ = x₂ * r⁻¹ := (hXc x₂ hx₂ r⁻¹ (R.inv_mem hr)).symm
    have h5 : x₃ = (x₁ * x₂) * (r⁻¹ * s⁻¹ * r * s) := by
      rw [h3]
      calc x₁ * r⁻¹ * (x₂ * s⁻¹) * (r * s) = x₁ * (r⁻¹ * x₂) * s⁻¹ * (r * s) := by group
        _ = x₁ * (x₂ * r⁻¹) * s⁻¹ * (r * s) := by rw [h4]
        _ = (x₁ * x₂) * (r⁻¹ * s⁻¹ * r * s) := by group
    have h6 : r⁻¹ * s⁻¹ * r * s = (x₁ * x₂)⁻¹ * x₃ := by
      rw [h5]; group
    rw [h6]
    exact X.mul_mem (X.inv_mem (X.mul_mem hx₁ hx₂)) hx₃
  have := key r⁻¹ (R.inv_mem hr) s⁻¹ (R.inv_mem hs)
  simpa [commutatorElement_def] using this

theorem t6_pow_mul {R X : Subgroup G} (hXc : ∀ x ∈ X, ∀ r ∈ R, x * r = r * x)
    (hcomm : ∀ r ∈ R, ∀ s ∈ R, ⁅r, s⁆ ∈ X) {s t : G} (hs : s ∈ R) (ht : t ∈ R) (n : ℕ) :
    ∃ x ∈ X, (s * t) ^ n = s ^ n * t ^ n * x := by
  induction n with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨x, hx, hxn⟩ := ih
    have hc₀ : ⁅t ^ n, s⁆ ∈ X := hcomm _ (R.pow_mem ht n) s hs
    set c₀ : G := ⁅t ^ n, s⁆ with hc₀def
    have hc₀s : c₀ * s = s * c₀ := hXc c₀ hc₀ s hs
    have hc₀t : c₀ * t = t * c₀ := hXc c₀ hc₀ t ht
    have hxs : x * s = s * x := hXc x hx s hs
    have hxt : x * t = t * x := hXc x hx t ht
    have hts : t ^ n * s = s * t ^ n * c₀ := by
      have : t ^ n * s = c₀ * (s * t ^ n) := by rw [hc₀def, commutatorElement_def]; group
      rw [this]
      calc c₀ * (s * t ^ n) = (c₀ * s) * t ^ n := by group
        _ = (s * c₀) * t ^ n := by rw [hc₀s]
        _ = s * (c₀ * t ^ n) := by group
        _ = s * (t ^ n * c₀) := by
          congr 1
          exact (hXc c₀ hc₀ (t ^ n) (R.pow_mem ht n))
        _ = s * t ^ n * c₀ := by group
    refine ⟨c₀ * x, X.mul_mem hc₀ hx, ?_⟩
    calc (s * t) ^ (n + 1) = (s * t) ^ n * (s * t) := pow_succ _ _
      _ = (s ^ n * t ^ n * x) * (s * t) := by rw [hxn]
      _ = s ^ n * t ^ n * (x * s) * t := by group
      _ = s ^ n * t ^ n * (s * x) * t := by rw [hxs]
      _ = s ^ n * (t ^ n * s) * x * t := by group
      _ = s ^ n * (s * t ^ n * c₀) * x * t := by rw [hts]
      _ = s ^ n * s * t ^ n * (c₀ * x * t) := by group
      _ = s ^ n * s * t ^ n * (t * (c₀ * x)) := by
          congr 1
          calc c₀ * x * t = c₀ * (x * t) := by group
            _ = c₀ * (t * x) := by rw [hxt]
            _ = (c₀ * t) * x := by group
            _ = (t * c₀) * x := by rw [hc₀t]
            _ = t * (c₀ * x) := by group
      _ = s ^ (n + 1) * t ^ (n + 1) * (c₀ * x) := by group

end CFSG.GH74.GLS.Stage4.Rest.T6
