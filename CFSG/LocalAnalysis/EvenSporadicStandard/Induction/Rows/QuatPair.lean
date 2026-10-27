module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Induction.CoverFix

open Subgroup

structure Q8Rel {G : Type*} [Group G] (x y : G) : Prop where
  sq_eq : x * x = y * y
  sq_ne : x * x ≠ 1
  conj_eq : x * y * x = y

namespace Q8Rel

variable {G : Type*} [Group G] {x y : G}

theorem yx_eq (h : Q8Rel x y) : y * x = x⁻¹ * y := by
  have := h.conj_eq
  calc y * x = x⁻¹ * (x * y * x) := by group
    _ = x⁻¹ * y := by rw [this]

theorem pow_four (h : Q8Rel x y) : (x * x) * (x * x) = 1 := by
  have h1 : y * (x * x) = x⁻¹ * x⁻¹ * y := by
    calc y * (x * x) = (y * x) * x := by group
      _ = x⁻¹ * y * x := by rw [h.yx_eq]
      _ = x⁻¹ * (y * x) := by group
      _ = x⁻¹ * (x⁻¹ * y) := by rw [h.yx_eq]
      _ = x⁻¹ * x⁻¹ * y := by group
  have h2 : y * (x * x) = (x * x) * y := by
    rw [h.sq_eq]
    group
  have h3 : (x * x) * y = (x⁻¹ * x⁻¹) * y := by rw [← h2, h1]
  have h4 : x * x = x⁻¹ * x⁻¹ := mul_right_cancel h3
  calc x * x * (x * x) = (x * x) * (x⁻¹ * x⁻¹) := by rw [← h4]
    _ = 1 := by group

theorem orderOf_eq_four (h : Q8Rel x y) : orderOf x = 4 := by
  have h4 : x ^ 2 ^ (1 + 1) = 1 := by
    have := h.pow_four
    calc x ^ 2 ^ (1 + 1) = (x * x) * (x * x) := by
          rw [show 2 ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two]
      _ = 1 := this
  have h2 : ¬ x ^ 2 ^ 1 = 1 := by
    intro h2
    exact h.sq_ne (by rw [← pow_two]; simpa using h2)
  have := orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4
  simpa using this

theorem not_commute (h : Q8Rel x y) : x * y ≠ y * x := by
  intro hc
  have h1 : y * x * x = y := by
    calc y * x * x = x * y * x := by rw [hc]
      _ = y := h.conj_eq
  apply h.sq_ne
  have : y * (x * x) = y * 1 := by
    rw [mul_one]
    calc y * (x * x) = y * x * x := by group
      _ = y := h1
  exact mul_left_cancel this

theorem y_not_mem_zpowers (h : Q8Rel x y) : y ∉ zpowers x := by
  intro hy
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy
  apply h.not_commute
  rw [← hn]
  exact (Commute.zpow_right (Commute.refl x) n).eq

end Q8Rel

theorem Q8Rel.map {G H : Type*} [Group G] [Group H] {x y : G} (h : Q8Rel x y) (f : G →* H)
    (hf : Function.Injective f) : Q8Rel (f x) (f y) where
  sq_eq := by rw [← map_mul, ← map_mul, h.sq_eq]
  sq_ne := fun h1 => h.sq_ne (hf (by rw [map_mul, h1, map_one]))
  conj_eq := by rw [← map_mul, ← map_mul, h.conj_eq]

theorem Q8Rel.of_map {G H : Type*} [Group G] [Group H] {x y : G} (f : G →* H)
    (hf : Function.Injective f) (h : Q8Rel (f x) (f y)) : Q8Rel x y where
  sq_eq := hf (by rw [map_mul, map_mul]; exact h.sq_eq)
  sq_ne := fun h1 => h.sq_ne (by rw [← map_mul, h1, map_one])
  conj_eq := hf (by rw [map_mul, map_mul]; exact h.conj_eq)

variable {G : Type*} [Group G]

theorem card_closure_q8 {x y : G} (h : Q8Rel x y) : Nat.card ↥(closure ({x, y} : Set G)) = 8 := by
  set Q : Subgroup G := closure ({x, y} : Set G) with hQ
  set H : Subgroup G := zpowers x with hH
  have hx : x ∈ Q := subset_closure (Set.mem_insert _ _)
  have hy : y ∈ Q := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hHQ : H ≤ Q := by
    rw [hH, zpowers_le]
    exact hx
  have hyinv : y⁻¹ = y * (x⁻¹ * x⁻¹) := by
    have : y * y = x * x := h.sq_eq.symm
    calc y⁻¹ = y⁻¹ * (y * y) * (y * y)⁻¹ := by group
      _ = y * (y * y)⁻¹ := by group
      _ = y * (x * x)⁻¹ := by rw [this]
      _ = y * (x⁻¹ * x⁻¹) := by group
  have hxsq : x * x ∈ H := H.mul_mem (mem_zpowers x) (mem_zpowers x)
  have hconj : ∀ k ∈ H, y * k * y⁻¹ ∈ H := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h1 : y * x * y⁻¹ = x⁻¹ := by
      calc y * x * y⁻¹ = x⁻¹ * y * y⁻¹ := by rw [h.yx_eq]
        _ = x⁻¹ := by group
    have : y * x ^ n * y⁻¹ = (y * x * y⁻¹) ^ n := conj_zpow.symm
    rw [this, h1]
    exact H.zpow_mem (H.inv_mem (mem_zpowers x)) n
  have hT : ∀ g ∈ Q, g ∈ H ∨ ∃ k ∈ H, g = k * y := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with rfl | rfl
      · exact Or.inl (mem_zpowers _)
      · exact Or.inr ⟨1, H.one_mem, by group⟩
    | one => exact Or.inl H.one_mem
    | mul g₁ g₂ _ _ ih₁ ih₂ =>
      rcases ih₁ with h₁ | ⟨k₁, hk₁, rfl⟩
      · rcases ih₂ with h₂ | ⟨k₂, hk₂, rfl⟩
        · exact Or.inl (H.mul_mem h₁ h₂)
        · exact Or.inr ⟨g₁ * k₂, H.mul_mem h₁ hk₂, by group⟩
      · rcases ih₂ with h₂ | ⟨k₂, hk₂, rfl⟩
        · refine Or.inr ⟨k₁ * (y * g₂ * y⁻¹), H.mul_mem hk₁ (hconj g₂ h₂), by group⟩
        · refine Or.inl ?_
          have e : k₁ * y * (k₂ * y) = k₁ * (y * k₂ * y⁻¹) * (y * y) := by group
          rw [e, h.sq_eq.symm]
          exact H.mul_mem (H.mul_mem hk₁ (hconj k₂ hk₂)) hxsq
    | inv g _ ih =>
      rcases ih with h₁ | ⟨k₁, hk₁, rfl⟩
      · exact Or.inl (H.inv_mem h₁)
      · refine Or.inr ⟨y * (x⁻¹ * x⁻¹ * k₁⁻¹) * y⁻¹, ?_, ?_⟩
        · exact hconj _ (H.mul_mem (H.mul_mem (H.inv_mem (mem_zpowers x))
            (H.inv_mem (mem_zpowers x))) (H.inv_mem hk₁))
        · calc (k₁ * y)⁻¹ = y⁻¹ * k₁⁻¹ := by group
            _ = (y * (x⁻¹ * x⁻¹)) * k₁⁻¹ := by rw [hyinv]
            _ = y * (x⁻¹ * x⁻¹ * k₁⁻¹) * y⁻¹ * y := by group
  have hidx : (H.subgroupOf Q).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hy⟩, fun b => ?_⟩
    have hyH : y ∉ H := h.y_not_mem_zpowers
    obtain ⟨b, hbQ⟩ := b
    show Xor (b * y ∈ H) (b ∈ H)
    rcases hT b hbQ with hb | ⟨k, hk, rfl⟩
    · refine Or.inr ⟨hb, fun hby => hyH ?_⟩
      have := H.mul_mem (H.inv_mem hb) hby
      simpa using this
    · refine Or.inl ⟨?_, fun hb => hyH ?_⟩
      · have e : k * y * y = k * (x * x) := by
          calc k * y * y = k * (y * y) := by group
            _ = k * (x * x) := by rw [h.sq_eq.symm]
        rw [e]
        exact H.mul_mem hk hxsq
      · have := H.mul_mem (H.inv_mem hk) hb
        simpa using this
  have hcard := Subgroup.card_mul_index (H.subgroupOf Q)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHQ).toEquiv, hH, Nat.card_zpowers,
    h.orderOf_eq_four] at hcard
  omega

section Lift

variable {K : Type*} [Group K]

theorem sq_commute_right {a b : K} (h2 : a * a * (b * b)⁻¹ ∈ center K) :
    a * a * b = b * (a * a) := by
  have hc := mem_center_iff.1 h2
  have e : a * a = (a * a * (b * b)⁻¹) * (b * b) := by group
  calc a * a * b = ((a * a * (b * b)⁻¹) * (b * b)) * b := by rw [← e]
    _ = (a * a * (b * b)⁻¹) * (b * b * b) := by group
    _ = (a * a * (b * b)⁻¹) * (b * (b * b)) := by group
    _ = b * ((a * a * (b * b)⁻¹) * (b * b)) := by rw [← mul_assoc, ← hc b]; group
    _ = b * (a * a) := by rw [← e]

theorem commutator_sq_eq_one {a b : K} (h3 : b⁻¹ * a * b * a ∈ center K)
    (h2 : a * a * (b * b)⁻¹ ∈ center K) :
    (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1 := by
  set u : K := b⁻¹ * a * b * a with hu
  have hc3 := mem_center_iff.1 h3
  have hc2 := mem_center_iff.1 h2
  have h1 : a * b * a * b⁻¹ = u := by
    calc a * b * a * b⁻¹ = b * (b⁻¹ * a * b * a) * b⁻¹ := by group
      _ = b * u * b⁻¹ := rfl
      _ = u * b * b⁻¹ := by rw [hc3 b]
      _ = u := by group
  have h4 : b * a⁻¹ * b⁻¹ = u⁻¹ * a := by
    have e : b * a * b⁻¹ = a⁻¹ * u := by
      calc b * a * b⁻¹ = a⁻¹ * (a * b * a * b⁻¹) := by group
        _ = a⁻¹ * u := by rw [h1]
    calc b * a⁻¹ * b⁻¹ = (b * a * b⁻¹)⁻¹ := by group
      _ = (a⁻¹ * u)⁻¹ := by rw [e]
      _ = u⁻¹ * a := by group
  have h5 : a * b * a⁻¹ * b⁻¹ = u⁻¹ * (a * a) := by
    calc a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      _ = a * (u⁻¹ * a) := by rw [h4]
      _ = (a * u⁻¹) * a := by group
      _ = (u⁻¹ * a) * a := by rw [mem_center_iff.1 ((center K).inv_mem h3) a]
      _ = u⁻¹ * (a * a) := by group
  have h6 : (a * a) * (a * a) = u * u := by
    have e1 : b⁻¹ * a * b = u * a⁻¹ := by
      calc b⁻¹ * a * b = (b⁻¹ * a * b * a) * a⁻¹ := by group
        _ = u * a⁻¹ := rfl
    have e2 : b⁻¹ * (a * a) * b = a * a := by
      have := sq_commute_right h2
      calc b⁻¹ * (a * a) * b = b⁻¹ * (b * (a * a)) := by rw [← this]; group
        _ = a * a := by group
    have e3 : b⁻¹ * (a * a) * b = (u * a⁻¹) * (u * a⁻¹) := by
      rw [← e1]
      group
    have e4 : (u * a⁻¹) * (u * a⁻¹) = u * u * (a⁻¹ * a⁻¹) := by
      calc (u * a⁻¹) * (u * a⁻¹) = u * (a⁻¹ * u) * a⁻¹ := by group
        _ = u * (u * a⁻¹) * a⁻¹ := by rw [← hc3 a⁻¹]
        _ = u * u * (a⁻¹ * a⁻¹) := by group
    have e5 : a * a = u * u * (a⁻¹ * a⁻¹) := by rw [← e2, e3, e4]
    calc (a * a) * (a * a) = (u * u * (a⁻¹ * a⁻¹)) * (a * a) := by rw [← e5]
      _ = u * u := by group
  rw [h5]
  calc u⁻¹ * (a * a) * (u⁻¹ * (a * a)) = u⁻¹ * u⁻¹ * ((a * a) * (a * a)) := by
        calc u⁻¹ * (a * a) * (u⁻¹ * (a * a)) = u⁻¹ * ((a * a) * u⁻¹) * (a * a) := by group
          _ = u⁻¹ * (u⁻¹ * (a * a)) * (a * a) := by
            rw [(mem_center_iff.1 ((center K).inv_mem h3) (a * a))]
          _ = u⁻¹ * u⁻¹ * ((a * a) * (a * a)) := by group
    _ = u⁻¹ * u⁻¹ * (u * u) := by rw [h6]
    _ = 1 := by group

end Lift

end CFSG.EvenSporadicStandard.Induction.CoverFix
