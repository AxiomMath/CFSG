module

public import CFSG.CGT.Timmesfeld75.Config

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Cfg

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem eq_of_card_two_subgroup {K : Subgroup G} (h : Nat.card K = 2) {p q : G} (hp : p ∈ K)
    (hq : q ∈ K) (hp1 : p ≠ 1) (hq1 : q ≠ 1) : p = q := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : K)).1 h
  have h1 := huniq ⟨p, hp⟩ (fun h => hp1 (congrArg Subtype.val h))
  have h2 := huniq ⟨q, hq⟩ (fun h => hq1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem Cfg.comm_ne_one (c : Cfg T T₁) {x y : G} (hx : x ∈ T) (hxL : x ∉ normIn T T₁)
    (hy : y ∈ normIn T₁ T) (hy1 : y ≠ 1) : ⁅x, y⁆ ≠ 1 := by
  intro h1
  have hxy : x * y = y * x := commutatorElement_eq_one_iff_mul_comm.1 h1
  have hyT₁ : y ∈ T₁ := normIn_le T₁ T hy
  have hx' : x ∈ Subgroup.normalizer (T₁ : Set G) :=
    c.wc₁.centralizer_le_normalizer hyT₁ hy1 (Subgroup.mem_centralizer_singleton_iff.2 hxy)
  exact hxL (mem_normIn.2 ⟨hx, hx'⟩)

theorem Cfg.conj_mul_eq_of_card_two (c : Cfg T T₁) (hcard : Nat.card (normIn T T₁) = 2)
    {x y l : G} (hx : x ∈ T) (hxL : x ∉ normIn T T₁) (hy : y ∈ normIn T₁ T) (hy1 : y ≠ 1)
    (hl : l ∈ normIn T T₁) (hl1 : l ≠ 1) : x * y * x⁻¹ = l * y := by
  have hc : ⁅x, y⁆ ∈ normIn T T₁ := c.comm_mem_normIn hx hy
  have heq : ⁅x, y⁆ = l := eq_of_card_two_subgroup hcard hc hl (c.comm_ne_one hx hxL hy hy1) hl1
  calc x * y * x⁻¹ = ⁅x, y⁆ * y := by
        simp only [commutatorElement_def]
        group
    _ = l * y := by rw [heq]

end Cfg

section Rel

variable {G : Type} [Group G]

theorem eq_of_relations {ℓ ℓ₁ a t t₁ t₂ : G}
    (hℓ : ℓ * ℓ = 1) (hℓ₁ : ℓ₁ * ℓ₁ = 1) (ha : a * a = 1) (hℓℓ₁ : ℓ * ℓ₁ = ℓ₁ * ℓ)
    (htℓ : t * ℓ * t⁻¹ = ℓ) (htℓ₁ : t * ℓ₁ * t⁻¹ = ℓ * ℓ₁) (hta : t * a * t⁻¹ = ℓ * a)
    (ht₁ℓ : t₁ * ℓ * t₁⁻¹ = ℓ₁ * ℓ) (ht₁ℓ₁ : t₁ * ℓ₁ * t₁⁻¹ = ℓ₁)
    (ht₁a : t₁ * a * t₁⁻¹ = ℓ₁ * a) (ht₂ℓ : t₂ * ℓ * t₂⁻¹ = a * ℓ)
    (ht₂ℓ₁ : t₂ * ℓ₁ * t₂⁻¹ = a * ℓ₁) (ht₂a : t₂ * a * t₂⁻¹ = a) {m : ℕ} (hm : Odd m)
    (hz : (t₂ * t * t₁ * t) ^ m * ℓ = ℓ * (t₂ * t * t₁ * t) ^ m) : a * ℓ₁ = ℓ := by
  set z : G := t₂ * t * t₁ * t with hzdef
  have c1 : ℓ * ℓ₁ * ℓ = ℓ₁ := by
    calc ℓ * ℓ₁ * ℓ = ℓ₁ * ℓ * ℓ := by rw [hℓℓ₁]
      _ = ℓ₁ := by rw [mul_assoc, hℓ, mul_one]
  have c2 : ℓ₁ * ℓ * ℓ₁ = ℓ := by
    calc ℓ₁ * ℓ * ℓ₁ = ℓ * ℓ₁ * ℓ₁ := by rw [← hℓℓ₁]
      _ = ℓ := by rw [mul_assoc, hℓ₁, mul_one]
  have hconj : ∀ x : G, z * x * z⁻¹ = t₂ * (t * (t₁ * (t * x * t⁻¹) * t₁⁻¹) * t⁻¹) * t₂⁻¹ := by
    intro x
    rw [hzdef]
    group
  have hmul : ∀ (g x y : G), g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by
    intro g x y
    group
  have hzℓ : z * ℓ * z⁻¹ = a * ℓ₁ := by
    rw [hconj, htℓ, ht₁ℓ, hmul t ℓ₁ ℓ, htℓ₁, htℓ, c1, ht₂ℓ₁]
  have hzℓ₁ : z * ℓ₁ * z⁻¹ = a * ℓ := by
    rw [hconj, htℓ₁, hmul t₁ ℓ ℓ₁, ht₁ℓ, ht₁ℓ₁, c2, htℓ, ht₂ℓ]
  have hza : z * a * z⁻¹ = a := by
    rw [hconj, hta, hmul t₁ ℓ a, ht₁ℓ, ht₁a]
    have e3 : ℓ₁ * ℓ * (ℓ₁ * a) = ℓ * a := by
      calc ℓ₁ * ℓ * (ℓ₁ * a) = (ℓ₁ * ℓ * ℓ₁) * a := by group
        _ = ℓ * a := by rw [c2]
    rw [e3, hmul t ℓ a, htℓ, hta]
    have e5 : ℓ * (ℓ * a) = a := by rw [← mul_assoc, hℓ, one_mul]
    rw [e5, ht₂a]
  have hzz : ∀ x : G, z * z * x * (z * z)⁻¹ = z * (z * x * z⁻¹) * z⁻¹ := by
    intro x
    group
  have h2ℓ₁ : z * z * ℓ₁ * (z * z)⁻¹ = ℓ₁ := by
    rw [hzz, hzℓ₁, hmul z a ℓ, hza, hzℓ, ← mul_assoc, ha, one_mul]
  have h2a : z * z * a * (z * z)⁻¹ = a := by rw [hzz, hza, hza]
  have hcomm : Commute (z * z) (a * ℓ₁) := by
    have h3 : z * z * (a * ℓ₁) * (z * z)⁻¹ = a * ℓ₁ := by
      rw [hmul (z * z) a ℓ₁, h2a, h2ℓ₁]
    exact mul_inv_eq_iff_eq_mul.1 h3
  obtain ⟨k, hk⟩ := hm
  have hzm : z ^ m = (z * z) ^ k * z := by
    rw [hk, pow_succ, pow_mul, pow_two]
  have hcommk : Commute ((z * z) ^ k) (a * ℓ₁) := hcomm.pow_left k
  have h1 : z ^ m * ℓ * (z ^ m)⁻¹ = ℓ := mul_inv_eq_iff_eq_mul.2 hz
  have h2 : z ^ m * ℓ * (z ^ m)⁻¹ = a * ℓ₁ := by
    rw [hzm]
    have e : ∀ u : G, u * z * ℓ * (u * z)⁻¹ = u * (z * ℓ * z⁻¹) * u⁻¹ := by
      intro u
      group
    rw [e, hzℓ]
    exact mul_inv_eq_iff_eq_mul.2 hcommk.eq
  exact h2.symm.trans h1

end Rel

end CFSG.CGT.Timmesfeld75
