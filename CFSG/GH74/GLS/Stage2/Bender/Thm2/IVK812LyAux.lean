module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Subgroup

private lemma eq_or_eq_inv_of_mem_zpowers_of_orderOf {X : Type*} [Group X] {x y : X}
    (hx : orderOf x = 3) (hy : y ∈ zpowers x) (hyo : orderOf y = 3) : y = x ∨ y = x⁻¹ := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hk : x ^ k = x ^ (k % 3) := by
    rw [← zpow_mod_orderOf, hx]; rfl
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [hk, h0, zpow_zero, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  · left; rw [hk, h1, zpow_one]
  · right
    rw [hk, h2]
    have : x ^ (2 : ℤ) * x = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_succ]
      exact hx3
    exact eq_inv_of_mul_eq_one_left this

private lemma exists_sign_of_mem_normalizer {X : Type*} [Group X] {x a : X} (hx : orderOf x = 3)
    (ha : a ∈ normalizer (zpowers x : Set X)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ a * x * a⁻¹ = x ^ ε ∧ a⁻¹ * x * a = x ^ ε := by
  have hord : orderOf (a * x * a⁻¹) = 3 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hx]
  have hmem : a * x * a⁻¹ ∈ zpowers x := (mem_normalizer_iff.1 ha x).1 (mem_zpowers x)
  rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf hx hmem hord with h | h
  · refine ⟨1, Or.inl rfl, by rw [h, zpow_one], ?_⟩
    rw [zpow_one]
    calc a⁻¹ * x * a = a⁻¹ * (a * x * a⁻¹) * a := by rw [h]
      _ = x := by group
  · refine ⟨-1, Or.inr rfl, by rw [h, zpow_neg_one], ?_⟩
    rw [zpow_neg_one]
    calc a⁻¹ * x * a = a⁻¹ * (a * x * a⁻¹)⁻¹ * a := by rw [h, inv_inv]
      _ = x⁻¹ := by group

private lemma conj_zpow_of_eq {X : Type*} [Group X] {x g : X} {ε : ℤ} (h : g * x * g⁻¹ = x ^ ε)
    (k : ℤ) : g * x ^ k * g⁻¹ = x ^ (ε * k) := by
  rw [← conj_zpow, h, ← zpow_mul]

private lemma inv_conj_zpow_of_eq {X : Type*} [Group X] {x g : X} {ε : ℤ}
    (h : g⁻¹ * x * g = x ^ ε) (k : ℤ) : g⁻¹ * x ^ k * g = x ^ (ε * k) := by
  have := conj_zpow_of_eq (g := g⁻¹) (x := x) (ε := ε) (by rwa [inv_inv]) k
  rwa [inv_inv] at this

theorem commutator_le_centralizer_of_le_normalizer_zpowers {X : Type*} [Group X] {x : X}
    (hx : orderOf x = 3) {A : Subgroup X}
    (hA : A ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X)) :
    ⁅A, A⁆ ≤ Subgroup.centralizer ({x} : Set X) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨α, hα, ha1, ha2⟩ := exists_sign_of_mem_normalizer hx (hA ha)
  obtain ⟨β, hβ, hb1, hb2⟩ := exists_sign_of_mem_normalizer hx (hA hb)
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  have hαβ : α * (β * (α * β)) = 1 := by
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> norm_num
  refine mul_inv_eq_iff_eq_mul.1 ?_
  calc a * b * a⁻¹ * b⁻¹ * x * (a * b * a⁻¹ * b⁻¹)⁻¹
      = a * (b * (a⁻¹ * (b⁻¹ * x * b) * a) * b⁻¹) * a⁻¹ := by group
    _ = a * (b * (a⁻¹ * x ^ β * a) * b⁻¹) * a⁻¹ := by rw [hb2]
    _ = a * (b * x ^ (α * β) * b⁻¹) * a⁻¹ := by rw [inv_conj_zpow_of_eq ha2 β]
    _ = a * x ^ (β * (α * β)) * a⁻¹ := by rw [conj_zpow_of_eq hb1 (α * β)]
    _ = x ^ (α * (β * (α * β))) := conj_zpow_of_eq ha1 _
    _ = x := by rw [hαβ, zpow_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
