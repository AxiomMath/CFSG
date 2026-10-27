module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2TableDefs
public import Mathlib.Data.List.Dedup

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TableX

structure CheckSpec0 (n : ℕ) (inn : ℕ → Bool) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : Prop where
  n_eq : n = 256
  tI_lt : tI < n
  inn_zero : inn 0 = true
  inn_t : inn tI = true
  roots_ge : 20 ≤ (rootsIn n inn mul tI).length
  inn_closed : ∀ a, a < n → inn a = true → ∀ b, b < n → inn b = true → inn (mul a b) = true
  inv : ∀ a, a < n → ∃ b, b < n ∧ mul a b = 0
  t_central : ∀ a, a < n → mul a tI = mul tI a
  E_zero : 0 ∈ eListX n inn mul tI
  E_t : tI ∈ eListX n inn mul tI
  E_roots : ∀ a ∈ rootsIn n inn mul tI, a ∈ eListX n inn mul tI
  E_mul : ∀ a ∈ eListX n inn mul tI, ∀ b ∈ eListX n inn mul tI, mul a b ∈ eListX n inn mul tI
  E_inv : ∀ a ∈ eListX n inn mul tI, ∃ b ∈ eListX n inn mul tI, mul a b = 0
  E_prod_roots : ∀ a ∈ eListX n inn mul tI, a = 0 ∨ a ∈ rootsIn n inn mul tI ∨
    ∃ x ∈ rootsIn n inn mul tI, ∃ y ∈ rootsIn n inn mul tI, mul x y = a
  E_prod_invol : ∀ a ∈ eListX n inn mul tI, a = 0 ∨
    (a ∈ eListX n inn mul tI ∧ mul a a = 0 ∧ a ≠ 0) ∨
    ∃ x ∈ eListX n inn mul tI, mul x x = 0 ∧ x ≠ 0 ∧
      ∃ y ∈ eListX n inn mul tI, mul y y = 0 ∧ y ≠ 0 ∧ mul x y = a
  t_invol : mul tI tI = 0 ∧ tI ≠ 0
  E_nonab : ∃ a ∈ eListX n inn mul tI, ∃ b ∈ eListX n inn mul tI, mul a b ≠ mul b a
  E_comm : ∀ a ∈ eListX n inn mul tI, ∀ b ∈ eListX n inn mul tI,
    mul a b = mul b a ∨ mul a b = mul (mul b a) tI
  E_center : ∀ y ∈ eListX n inn mul tI, (∀ f ∈ eListX n inn mul tI, mul f y = mul y f) →
    y = 0 ∨ y = tI
  K_center : ∀ s, s < n → (∀ x, x < n → mul x s = mul s x) → s = 0 ∨ s = tI
  K_cent : ∀ s, s < n → (∀ e ∈ eListX n inn mul tI, mul s e = mul e s) → s = 0 ∨ s = tI
  sqrt_lt : ∀ c, c < n → mul c c = 0 → c ≠ 0 → c ≠ tI →
    ((List.range n).filter fun a => mul a a == c).length < 20
  outer_nbr : ∀ a, a < n → inn a = false → mul a a = tI → nbrCount n mul tI a < 19

theorem mem_innList {n : ℕ} {inn : ℕ → Bool} {a : ℕ} :
    a ∈ innList n inn ↔ a < n ∧ inn a = true := by
  simp [innList, List.mem_filter, List.mem_range]

theorem mem_rootsIn {n : ℕ} {inn : ℕ → Bool} {mul : ℕ → ℕ → ℕ} {tI a : ℕ} :
    a ∈ rootsIn n inn mul tI ↔ (a < n ∧ inn a = true) ∧ mul a a = tI := by
  simp [rootsIn, mem_innList, List.mem_filter]

theorem mem_eListX {n : ℕ} {inn : ℕ → Bool} {mul : ℕ → ℕ → ℕ} {tI a : ℕ} :
    a ∈ eListX n inn mul tI ↔ a = 0 ∨ a ∈ rootsIn n inn mul tI ∨
      ∃ x ∈ rootsIn n inn mul tI, ∃ y ∈ rootsIn n inn mul tI, mul x y = a := by
  simp [eListX, List.mem_dedup, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]

end CFSG.EvenSporadicStandard.Fin76b.TableX
