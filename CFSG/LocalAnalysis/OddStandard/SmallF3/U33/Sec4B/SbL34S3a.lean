module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.L34Z

open Equiv

@[expose] def klein4_a : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def klein4_b : Perm (Fin 4) := swap 0 2 * swap 1 3

@[expose] def klein4 : Subgroup (Perm (Fin 4)) where
  carrier := {g | g = 1 ∨ g = klein4_a ∨ g = klein4_b ∨ g = klein4_a * klein4_b}
  mul_mem' := by
    have h : ∀ a b : Perm (Fin 4),
        (a = 1 ∨ a = klein4_a ∨ a = klein4_b ∨ a = klein4_a * klein4_b) →
        (b = 1 ∨ b = klein4_a ∨ b = klein4_b ∨ b = klein4_a * klein4_b) →
        a * b = 1 ∨ a * b = klein4_a ∨ a * b = klein4_b ∨ a * b = klein4_a * klein4_b := by
      decide +kernel
    exact fun {a b} ha hb => h a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := by
    have h : ∀ a : Perm (Fin 4),
        (a = 1 ∨ a = klein4_a ∨ a = klein4_b ∨ a = klein4_a * klein4_b) →
        a⁻¹ = 1 ∨ a⁻¹ = klein4_a ∨ a⁻¹ = klein4_b ∨ a⁻¹ = klein4_a * klein4_b := by
      decide +kernel
    exact fun {a} ha => h a ha

theorem mem_klein4_iff (g : Perm (Fin 4)) :
    g ∈ klein4 ↔ g = 1 ∨ g = klein4_a ∨ g = klein4_b ∨ g = klein4_a * klein4_b := Iff.rfl

instance klein4_normal : klein4.Normal where
  conj_mem n hn g := by
    have h : ∀ n g : Perm (Fin 4),
        (n = 1 ∨ n = klein4_a ∨ n = klein4_b ∨ n = klein4_a * klein4_b) →
        g * n * g⁻¹ = 1 ∨ g * n * g⁻¹ = klein4_a ∨ g * n * g⁻¹ = klein4_b ∨
          g * n * g⁻¹ = klein4_a * klein4_b := by
      decide +kernel
    exact h n g hn

theorem card_klein4 : Nat.card klein4 = 4 := by
  rw [Nat.subtype_card ({1, klein4_a, klein4_b, klein4_a * klein4_b} : Finset (Perm (Fin 4)))
    (fun g => by simp [mem_klein4_iff])]
  decide +kernel

theorem klein4_sq {g : Perm (Fin 4)} (hg : g ∈ klein4) : g * g = 1 := by
  have h : ∀ g : Perm (Fin 4),
      (g = 1 ∨ g = klein4_a ∨ g = klein4_b ∨ g = klein4_a * klein4_b) → g * g = 1 := by
    decide +kernel
  exact h g ((mem_klein4_iff g).mp hg)

theorem klein4_comm {g h : Perm (Fin 4)} (hg : g ∈ klein4) (hh : h ∈ klein4) :
    g * h = h * g := by
  have h' : ∀ g h : Perm (Fin 4),
      (g = 1 ∨ g = klein4_a ∨ g = klein4_b ∨ g = klein4_a * klein4_b) →
      (h = 1 ∨ h = klein4_a ∨ h = klein4_b ∨ h = klein4_a * klein4_b) → g * h = h * g := by
    decide +kernel
  exact h' g h ((mem_klein4_iff g).mp hg) ((mem_klein4_iff h).mp hh)

theorem exists_conj_of_three {c c' : Perm (Fin 4)} (hc : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hc' : c' ^ 3 = 1) (hc'1 : c' ≠ 1) : ∃ g : Perm (Fin 4), g * c * g⁻¹ = c' := by
  revert c c'
  decide +kernel

theorem eq_one_of_mem_klein4_cent_three {c k : Perm (Fin 4)} (hc : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hk : k ∈ klein4) (hkc : k * c = c * k) : k = 1 := by
  have h : ∀ c k : Perm (Fin 4),
      (k = 1 ∨ k = klein4_a ∨ k = klein4_b ∨ k = klein4_a * klein4_b) →
      c ^ 3 = 1 → c ≠ 1 → k * c = c * k → k = 1 := by
    decide +kernel
  exact h c k ((mem_klein4_iff k).mp hk) hc hc1 hkc

private theorem exists_conj_mul_pow_three (g : Perm (Fin 4)) (hg : g ∉ klein4) :
    ∃ a b : Perm (Fin 4),
      ((a * g * a⁻¹) * (b * g * b⁻¹)) ^ 3 = 1 ∧
        (a * g * a⁻¹) * (b * g * b⁻¹) ≠ 1 := by
  rw [mem_klein4_iff] at hg
  have h : ∀ g : Perm (Fin 4),
      ¬ (g = 1 ∨ g = klein4_a ∨ g = klein4_b ∨ g = klein4_a * klein4_b) →
      ∃ a b : Perm (Fin 4),
        ((a * g * a⁻¹) * (b * g * b⁻¹)) ^ 3 = 1 ∧
          (a * g * a⁻¹) * (b * g * b⁻¹) ≠ 1 := by
    decide +kernel
  exact h g hg

theorem normal_le_klein4 (N : Subgroup (Perm (Fin 4))) [N.Normal]
    (hN : ∀ c ∈ N, c ^ 3 = 1 → c = 1) : N ≤ klein4 := by
  intro g hg
  by_contra hgk
  obtain ⟨a, b, h3, h1⟩ := exists_conj_mul_pow_three g hgk
  have ha : a * g * a⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem g hg a
  have hb : b * g * b⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem g hg b
  exact h1 (hN _ (N.mul_mem ha hb) h3)

theorem eq_klein4_of_normal (N : Subgroup (Perm (Fin 4))) [N.Normal]
    (hN : ∀ c ∈ N, c ^ 3 = 1 → c = 1) (h4 : 4 ≤ Nat.card N) : N = klein4 :=
  Subgroup.eq_of_le_of_card_ge (normal_le_klein4 N hN) (by rw [card_klein4]; exact h4)

end CFSG.OddStandard.SmallF3.HarrisU33.L34Z
