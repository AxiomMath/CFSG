module

public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

theorem comm_mem_of_sq_mem_of_conj_mem {N : Subgroup G} {x y : G}
    (hyN : ∀ n ∈ N, y⁻¹ * n * y ∈ N) (hx2 : x ^ 2 ∈ N) (hy2 : y ^ 2 ∈ N)
    (hxy2 : (x * y) ^ 2 ∈ N) : x * y * x⁻¹ * y⁻¹ ∈ N := by
  have e : x * y * x⁻¹ * y⁻¹ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
    rw [sq, sq, sq]
    group
  rw [e]
  exact mul_mem (mul_mem hxy2 (hyN _ (inv_mem hx2))) (inv_mem hy2)

theorem sq_mem_of_sq_mul_inv_sq_mem {X A A₁ : Subgroup G}
    (hN : ∀ x ∈ X, ∀ b ∈ A₁, x * b * x⁻¹ ∈ A₁)
    (hcomm : ∀ x ∈ X, ∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ A)
    (hAc : ∀ x ∈ X, ∀ w ∈ A, x * w * x⁻¹ * w⁻¹ ∈ A₁)
    (hsq : ∀ x ∈ X, ∀ x' ∈ X, x ∉ A → x' ∉ A → x ^ 2 * (x' ^ 2)⁻¹ ∈ A₁)
    {x : G} (hx : x ∈ X) (hxA : x ∉ A) {y₁ y₂ : G} (hy₁ : y₁ ∈ X) (hy₂ : y₂ ∈ X)
    (hy₁A : y₁ ∉ A) (hy₂A : y₂ ∉ A) (hy₁₂A : y₁ * y₂ ∉ A) (hxy₁A : x * y₁ ∉ A)
    (hxy₂A : x * y₂ ∉ A) (hxy₁₂A : x * (y₁ * y₂) ∉ A) : x ^ 2 ∈ A₁ := by
  have hx2X : (x ^ 2)⁻¹ ∈ X := inv_mem (pow_mem hx 2)
  have hc : ∀ z ∈ X, z ∉ A → x * z ∉ A → x⁻¹ * z * x * z⁻¹ * x ^ 2 ∈ A₁ := by
    intro z hz hzA hxzA
    have h1 := hsq _ (mul_mem hx hz) x hx hxzA hxA
    have h2 := hsq z hz x hx hzA hxA
    rw [sq (x * z)] at h1
    have e : x⁻¹ * z * x * z⁻¹ * x ^ 2 = (x ^ 2)⁻¹ *
        (x * z * (x * z) * (x ^ 2)⁻¹ * (z ^ 2 * (x ^ 2)⁻¹)⁻¹) * ((x ^ 2)⁻¹)⁻¹ := by
      group
    rw [e]
    exact hN _ hx2X _ (mul_mem h1 (inv_mem h2))
  have hP₁ := hc y₁ hy₁ hy₁A hxy₁A
  have hP₂ := hc y₂ hy₂ hy₂A hxy₂A
  have hP₁₂ := hc (y₁ * y₂) (mul_mem hy₁ hy₂) hy₁₂A hxy₁₂A
  have hc₂ : x⁻¹ * y₂ * x * y₂⁻¹ ∈ A := by
    have := hcomm _ (inv_mem hx) _ hy₂
    simpa using this
  have hb := hAc y₁ hy₁ _ hc₂
  have e : x ^ 2 = (y₁ * (x⁻¹ * y₂ * x * y₂⁻¹) * y₁⁻¹ * (x⁻¹ * y₂ * x * y₂⁻¹)⁻¹) *
      (x⁻¹ * y₂ * x * y₂⁻¹ * x ^ 2) * (x⁻¹ * (y₁ * y₂) * x * (y₁ * y₂)⁻¹ * x ^ 2)⁻¹ *
      (x⁻¹ * y₁ * x * y₁⁻¹ * x ^ 2) := by
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hb hP₂) (inv_mem hP₁₂)) hP₁

theorem commute_of_sq_of_equivariant {U A : Subgroup G} {d : G} (f : G → G)
    (hAc : ∀ u ∈ U, ∀ b ∈ A, u * b = b * u) (hA2 : ∀ b ∈ A, b ^ 2 = 1)
    (hU2 : ∀ u ∈ U, u ^ 2 ∈ A) (hdU : ∀ u ∈ U, d⁻¹ * u * d ∈ U)
    (htr : ∀ b ∈ A, ∀ b' ∈ A, b ≠ 1 → b' ≠ 1 → ∃ k : ℕ, (d ^ k)⁻¹ * b * d ^ k = b')
    (hfA : ∀ u ∈ U, f u ∈ A) (hfmul : ∀ u ∈ U, ∀ u' ∈ U, f (u * u') = f u * f u')
    (hfker : ∀ u ∈ U, f u = 1 ↔ u ∈ A)
    (hfeq : ∀ u ∈ U, f (d⁻¹ * u * d) = d⁻¹ * f u * d) :
    ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := by
  have hf1 : f 1 = 1 := (hfker 1 (one_mem _)).mpr (one_mem _)
  have hfinv : ∀ u ∈ U, f u⁻¹ = (f u)⁻¹ := fun u hu => by
    have := hfmul u⁻¹ (inv_mem hu) u hu
    rw [inv_mul_cancel, hf1] at this
    exact eq_inv_of_mul_eq_one_left this.symm
  have hdpow : ∀ k : ℕ, ∀ u ∈ U, (d ^ k)⁻¹ * u * d ^ k ∈ U ∧
      f ((d ^ k)⁻¹ * u * d ^ k) = (d ^ k)⁻¹ * f u * d ^ k := by
    intro k
    induction k with
    | zero => intro u hu; simpa using hu
    | succ k ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      have e : ∀ g : G, (d ^ (k + 1))⁻¹ * g * d ^ (k + 1) = d⁻¹ * ((d ^ k)⁻¹ * g * d ^ k) * d := by
        intro g
        rw [pow_succ]
        group
      rw [e, e, hfeq _ h1, h2]
      exact ⟨hdU _ h1, rfl⟩
  have hrel : ∀ u ∈ U, ∀ u' ∈ U, f u = f u' → u ^ 2 = u' ^ 2 := by
    intro u hu u' hu' he
    have hb : u⁻¹ * u' ∈ A := by
      rw [← hfker _ (mul_mem (inv_mem hu) hu'), hfmul _ (inv_mem hu) _ hu', hfinv u hu, he,
        inv_mul_cancel]
    obtain ⟨b, hbA, rfl⟩ : ∃ b ∈ A, u * b = u' := ⟨_, hb, by group⟩
    have hcomm := hAc u hu b hbA
    calc u ^ 2 = u ^ 2 * b ^ 2 := by rw [hA2 b hbA, mul_one]
      _ = u * (u * b) * b := by rw [sq, sq]; group
      _ = u * (b * u) * b := by rw [hcomm]
      _ = (u * b) ^ 2 := by rw [sq]; group
  have hsq : ∀ u ∈ U, ∀ u' ∈ U, (u * u') ^ 2 = u ^ 2 * u' ^ 2 := by
    by_cases hall : ∀ u ∈ U, u ^ 2 = 1
    · intro u hu u' hu'
      rw [hall _ (mul_mem hu hu'), hall u hu, hall u' hu', one_mul]
    push Not at hall
    obtain ⟨u₀, hu₀, hu₀2⟩ := hall
    have hu₀A : u₀ ∉ A := fun h => hu₀2 (hA2 u₀ h)
    have hb₀ : f u₀ ≠ 1 := fun h => hu₀A ((hfker u₀ hu₀).mp h)
    obtain ⟨j, hj⟩ := htr _ (hfA u₀ hu₀) _ (hU2 u₀ hu₀) hb₀ hu₀2
    have hform : ∀ u ∈ U, u ^ 2 = (d ^ j)⁻¹ * f u * d ^ j := by
      intro u hu
      by_cases huA : u ∈ A
      · rw [hA2 u huA, (hfker u hu).mpr huA]
        group
      have hfu : f u ≠ 1 := fun h => huA ((hfker u hu).mp h)
      obtain ⟨k, hk⟩ := htr _ (hfA u₀ hu₀) _ (hfA u hu) hb₀ hfu
      obtain ⟨hw, hfw⟩ := hdpow k u₀ hu₀
      have h1 : u ^ 2 = ((d ^ k)⁻¹ * u₀ * d ^ k) ^ 2 :=
        hrel u hu _ hw (by rw [hfw, hk])
      have hcomm : d ^ j * d ^ k = d ^ k * d ^ j := by rw [← pow_add, ← pow_add, add_comm]
      rw [h1, ← hk]
      calc ((d ^ k)⁻¹ * u₀ * d ^ k) ^ 2 = (d ^ k)⁻¹ * u₀ ^ 2 * d ^ k := by
            rw [sq, sq]; group
        _ = (d ^ k)⁻¹ * ((d ^ j)⁻¹ * f u₀ * d ^ j) * d ^ k := by rw [hj]
        _ = (d ^ j * d ^ k)⁻¹ * f u₀ * (d ^ j * d ^ k) := by group
        _ = (d ^ k * d ^ j)⁻¹ * f u₀ * (d ^ k * d ^ j) := by rw [hcomm]
        _ = (d ^ j)⁻¹ * ((d ^ k)⁻¹ * f u₀ * d ^ k) * d ^ j := by group
    intro u hu u' hu'
    rw [hform _ (mul_mem hu hu'), hform u hu, hform u' hu', hfmul u hu u' hu']
    group
  intro u hu u' hu'
  have h := hsq u hu u' hu'
  rw [sq, sq, sq] at h
  have h2 : u * (u' * u * u') = u * (u * u' * u') := by
    calc u * (u' * u * u') = u * u' * (u * u') := by group
      _ = u * u * (u' * u') := h
      _ = u * (u * u' * u') := by group
  have h3 := mul_right_cancel (mul_left_cancel h2)
  exact h3.symm

theorem exists_mem_not_mem_of_ncard_lt {H : Subgroup G} {S : Set G} (hfin : S.Finite)
    (hS : S.ncard < Nat.card H) : ∃ b ∈ H, b ∉ S := by
  by_contra hcon
  push Not at hcon
  have hsub : (H : Set G) ⊆ S := fun b hb => hcon b hb
  have h1 := Set.ncard_le_ncard hsub hfin
  rw [← Nat.card_coe_set_eq] at h1
  change Nat.card H ≤ S.ncard at h1
  omega

omit [Group G] in
theorem ncard_insert_four_le (a b c e : G) : ({a, b, c, e} : Set G).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a {b, c, e}
  have h2 := Set.ncard_insert_le b {c, e}
  have h3 := Set.ncard_insert_le c {e}
  rw [Set.ncard_singleton] at h3
  omega

end CFSG.SeitzReduction.RankOne
