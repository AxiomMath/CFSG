module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Tactic.Group

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem conj_of_free_series {M N : Subgroup G} {t : G} (htt : t * t = 1)
    (htN : t ∈ normalizer (N : Set G)) (hNM : N ≤ M) (hN2 : ∀ r ∈ N, r * r = 1)
    (hMN : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ N) (hM2 : ∀ x ∈ M, x * x ∈ N)
    (hfreeN : ∀ r ∈ N, t * r * t⁻¹ = r → ∃ s ∈ N, s * t * s⁻¹ * t⁻¹ = r)
    (hfreeM : ∀ x ∈ M, t * x * t⁻¹ * x⁻¹ ∈ N → ∃ w ∈ M, (w * t * w⁻¹ * t⁻¹)⁻¹ * x ∈ N)
    {x : G} (hx : x ∈ M) (hxt : x * t * (x * t) = 1) : ∃ w ∈ M, w * t * w⁻¹ = x * t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hMnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := fun m hm n hn => by
    have e : m * n * m⁻¹ = (m * n * m⁻¹ * n⁻¹) * n := by group
    rw [e]
    exact mul_mem (hMN m hm n (hNM hn)) hn
  have hconjN : ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun n hn => (mem_normalizer_iff.mp htN n).mp hn
  have htx : t * x * t⁻¹ = x⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [htinv]
    simpa [mul_assoc] using hxt
  have hker : t * x * t⁻¹ * x⁻¹ ∈ N := by
    rw [htx]
    exact hM2 _ (inv_mem hx)
  obtain ⟨w, hw, hwN⟩ := hfreeM x hx hker
  have hn₁ : t⁻¹ * ((w * t * w⁻¹ * t⁻¹)⁻¹ * x) * t ∈ N := by
    have h1 := hconjN _ hwN
    have e : t⁻¹ * ((w * t * w⁻¹ * t⁻¹)⁻¹ * x) * t =
        t * ((w * t * w⁻¹ * t⁻¹)⁻¹ * x) * t⁻¹ := by rw [htinv]
    rw [e]
    exact h1
  have hn₂ : w⁻¹ * (t⁻¹ * ((w * t * w⁻¹ * t⁻¹)⁻¹ * x) * t) * w ∈ N := by
    have h1 := hMnorm w⁻¹ (inv_mem hw) _ hn₁
    rwa [inv_inv] at h1
  have hnN := hconjN _ hn₂
  generalize hn : t * (w⁻¹ * (t⁻¹ * ((w * t * w⁻¹ * t⁻¹)⁻¹ * x) * t) * w) * t⁻¹ = n at hnN
  have hconj1 : w⁻¹ * (x * t) * w = n * t := by rw [← hn]; group
  have hinv2 : n * t * (n * t) = 1 := by
    rw [← hconj1]
    calc w⁻¹ * (x * t) * w * (w⁻¹ * (x * t) * w) = w⁻¹ * (x * t * (x * t)) * w := by group
      _ = 1 := by rw [hxt]; group
  have htn : t * n * t⁻¹ = n := by
    have h1 : t * n * t⁻¹ = n⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [htinv]
      simpa [mul_assoc] using hinv2
    rw [h1, inv_eq_of_mul_eq_one_right (hN2 n hnN)]
  obtain ⟨s, hs, hsn⟩ := hfreeN n hnN htn
  refine ⟨w * s, mul_mem hw (hNM hs), ?_⟩
  have h5 : s * t * s⁻¹ = n * t := by rw [← hsn]; group
  calc w * s * t * (w * s)⁻¹ = w * (s * t * s⁻¹) * w⁻¹ := by group
    _ = w * (n * t) * w⁻¹ := by rw [h5]
    _ = w * (w⁻¹ * (x * t) * w) * w⁻¹ := by rw [hconj1]
    _ = x * t := by group

end CFSG.SeitzReduction.RankOne
