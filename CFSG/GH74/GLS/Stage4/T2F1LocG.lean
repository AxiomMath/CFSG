module

public import CFSG.GH74.GLS.Stage4.T2F1LocTor
public import Mathlib.GroupTheory.Sylow

public noncomputable section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open Subgroup

section KT

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup_zpowers {K : Subgroup G} {t : G} (ht : t * t = 1)
    (hn : ∀ x ∈ K, t * x * t⁻¹ ∈ K) {y : G} (hy : y ∈ K ⊔ Subgroup.zpowers t) :
    ∃ k ∈ K, y = k ∨ y = k * t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hn' : ∀ x ∈ K, t⁻¹ * x * t ∈ K := fun x hx => by
    rw [hti]; have := hn x hx; rwa [hti] at this
  let P : Subgroup G :=
    { carrier := {y | ∃ k ∈ K, y = k ∨ y = k * t}
      one_mem' := ⟨1, K.one_mem, Or.inl rfl⟩
      mul_mem' := by
        rintro a b ⟨k₁, hk₁, h₁ | h₁⟩ ⟨k₂, hk₂, h₂ | h₂⟩
        · exact ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, Or.inl (by rw [h₁, h₂])⟩
        · exact ⟨k₁ * k₂, K.mul_mem hk₁ hk₂, Or.inr (by rw [h₁, h₂]; group)⟩
        · refine ⟨k₁ * (t * k₂ * t⁻¹), K.mul_mem hk₁ (hn k₂ hk₂), Or.inr ?_⟩
          rw [h₁, h₂]; group
        · refine ⟨k₁ * (t * k₂ * t⁻¹), K.mul_mem hk₁ (hn k₂ hk₂), Or.inl ?_⟩
          rw [h₁, h₂]
          calc k₁ * t * (k₂ * t) = k₁ * (t * k₂ * t⁻¹) * (t * t) := by group
            _ = k₁ * (t * k₂ * t⁻¹) := by rw [ht, mul_one]
      inv_mem' := by
        rintro a ⟨k, hk, h | h⟩
        · exact ⟨k⁻¹, K.inv_mem hk, Or.inl (by rw [h])⟩
        · refine ⟨t * k⁻¹ * t⁻¹, hn _ (K.inv_mem hk), Or.inr ?_⟩
          rw [h]
          calc (k * t)⁻¹ = t⁻¹ * k⁻¹ := by group
            _ = t * k⁻¹ := by rw [hti]
            _ = t * k⁻¹ * t⁻¹ * t := by group }
  have hle : K ⊔ Subgroup.zpowers t ≤ P := by
    refine sup_le (fun x hx => ⟨x, hx, Or.inl rfl⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨1, K.one_mem, Or.inr (by rw [one_mul])⟩
  exact hle hy

end KT

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem conj_sylow_onto (S₁ S₂ : Sylow 2 G) (c : G)
    (h : ∀ x ∈ (S₁ : Subgroup G), c * x * c⁻¹ ∈ (S₂ : Subgroup G)) :
    ∀ s ∈ (S₂ : Subgroup G), c⁻¹ * s * c ∈ (S₁ : Subgroup G) := by
  have hle : (S₁ : Subgroup G).map (MulAut.conj c).toMonoidHom ≤ (S₂ : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have hcard : Nat.card (S₂ : Subgroup G) ≤ Nat.card ((S₁ : Subgroup G).map (MulAut.conj c).toMonoidHom) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, Sylow.card_eq_multiplicity,
      Sylow.card_eq_multiplicity]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  intro s hs
  have : s ∈ (S₁ : Subgroup G).map (MulAut.conj c).toMonoidHom := by rw [heq]; exact hs
  obtain ⟨x, hx, hxs⟩ := this
  have : c⁻¹ * s * c = x := by
    rw [← hxs]
    simp [MulAut.conj_apply]
    group
  rw [this]; exact hx

end Sylow


section Conj

variable {G : Type} [Group G]

theorem exists_conj_eq_mul {K : Subgroup G} {t : G} (ht : t * t = 1)
    (hn : ∀ x ∈ K, t * x * t⁻¹ ∈ K) {c : G} (hc : c ∈ K ⊔ Subgroup.zpowers t) :
    ∃ k ∈ K, c⁻¹ * t * c = t * k := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hn' : ∀ x ∈ K, t⁻¹ * x * t ∈ K := fun x hx => by
    rw [hti]; have := hn x hx; rwa [hti] at this
  obtain ⟨k₀, hk₀, h | h⟩ := exists_mul_of_mem_sup_zpowers ht hn hc
  · refine ⟨(t⁻¹ * k₀⁻¹ * t) * k₀, K.mul_mem (hn' _ (K.inv_mem hk₀)) hk₀, ?_⟩
    rw [h]; group
  · refine ⟨t⁻¹ * ((t⁻¹ * k₀⁻¹ * t) * k₀) * t, hn' _ (K.mul_mem (hn' _ (K.inv_mem hk₀)) hk₀), ?_⟩
    rw [h]; group

end Conj

section Fixed

variable {G : Type} [Group G]

theorem mem_zpowers_sq_cases {z a : G} (hz : z * z = 1) (ha : a ∈ Subgroup.zpowers z) :
    a = 1 ∨ a = z := by
  obtain ⟨k, rfl⟩ := ha
  have hz2 : z ^ 2 = 1 := by rw [pow_two]; exact hz
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left; show z ^ (2 * m) = 1; rw [_root_.zpow_mul]; simp [hz2]
  · right; show z ^ (2 * m + 1) = z; rw [_root_.zpow_add, _root_.zpow_mul]; simp [hz2]

theorem fixed_of_prod_fixed {K₁ K₂ : Subgroup G} {z f : G} {r : ℕ}
    (hinter : K₁ ⊓ K₂ ≤ Subgroup.zpowers z) (hzz : z * z = 1) (hz1 : z ≠ 1)
    (hfK₁ : ∀ x ∈ K₁, f * x * f⁻¹ ∈ K₁) (hfK₂ : ∀ x ∈ K₂, f * x * f⁻¹ ∈ K₂)
    (hfz : f * z = z * f) (hfr : f ^ r = 1) (hr : Odd r) {k₁ k₂ : G} (hk₁ : k₁ ∈ K₁)
    (hk₂ : k₂ ∈ K₂) (hf : f * (k₁ * k₂) * f⁻¹ = k₁ * k₂) :
    f * k₁ * f⁻¹ = k₁ ∧ f * k₂ * f⁻¹ = k₂ := by
  have hfz' : f * z * f⁻¹ = z := by rw [hfz]; group
  have ha : f * k₁ * f⁻¹ ∈ K₁ := hfK₁ k₁ hk₁
  have hb : f * k₂ * f⁻¹ ∈ K₂ := hfK₂ k₂ hk₂
  have hab : (f * k₁ * f⁻¹) * (f * k₂ * f⁻¹) = k₁ * k₂ := by
    rw [← hf]; group
  have h1 : k₁⁻¹ * (f * k₁ * f⁻¹) = k₂ * (f * k₂ * f⁻¹)⁻¹ := by
    calc k₁⁻¹ * (f * k₁ * f⁻¹) = k₁⁻¹ * ((f * k₁ * f⁻¹) * (f * k₂ * f⁻¹)) * (f * k₂ * f⁻¹)⁻¹ := by
          group
      _ = k₂ * (f * k₂ * f⁻¹)⁻¹ := by rw [hab]; group
  have hε : k₁⁻¹ * (f * k₁ * f⁻¹) ∈ Subgroup.zpowers z :=
    hinter ⟨K₁.mul_mem (K₁.inv_mem hk₁) ha, h1 ▸ K₂.mul_mem hk₂ (K₂.inv_mem hb)⟩
  have hfk : f * k₁ * f⁻¹ = k₁ := by
    rcases mem_zpowers_sq_cases hzz hε with h | h
    · calc f * k₁ * f⁻¹ = k₁ * (k₁⁻¹ * (f * k₁ * f⁻¹)) := by group
        _ = k₁ := by rw [h, mul_one]
    · exfalso
      have hz : f * k₁ * f⁻¹ = k₁ * z := by
        calc f * k₁ * f⁻¹ = k₁ * (k₁⁻¹ * (f * k₁ * f⁻¹)) := by group
          _ = k₁ * z := by rw [h]
      have hj : ∀ j : ℕ, f ^ j * k₁ * (f ^ j)⁻¹ = k₁ * z ^ j := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have e : f ^ (j + 1) * k₁ * (f ^ (j + 1))⁻¹ = f * (f ^ j * k₁ * (f ^ j)⁻¹) * f⁻¹ := by
            rw [pow_succ']; group
          rw [e, ih]
          have hzj : f * z ^ j * f⁻¹ = z ^ j := by rw [← conj_pow, hfz']
          calc f * (k₁ * z ^ j) * f⁻¹ = (f * k₁ * f⁻¹) * (f * z ^ j * f⁻¹) := by group
            _ = k₁ * z ^ (j + 1) := by rw [hz, hzj, pow_succ']; group
      have h2 := hj r
      rw [hfr] at h2
      obtain ⟨m, rfl⟩ := hr
      have hzr : z ^ (2 * m + 1) = z := by
        rw [pow_succ, pow_mul, show z ^ 2 = 1 by rw [pow_two]; exact hzz]; simp
      rw [hzr] at h2
      simp only [inv_one, mul_one, one_mul] at h2
      exact hz1 (mul_left_cancel (a := k₁) (by rw [mul_one]; exact h2.symm))
  refine ⟨hfk, ?_⟩
  rw [hfk] at hab
  exact mul_left_cancel hab

end Fixed

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
