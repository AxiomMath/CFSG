module

import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM

section Cls

variable {Y : Type} [Group Y]

@[expose] def OConj (O : Subgroup Y) (a b : Y) : Prop :=
  ∃ o ∈ O, a = o * b * o⁻¹

theorem OConj.refl (O : Subgroup Y) (a : Y) : OConj O a a :=
  ⟨1, O.one_mem, by group⟩

theorem OConj.symm {O : Subgroup Y} {a b : Y} (h : OConj O a b) : OConj O b a := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨o⁻¹, O.inv_mem ho, by group⟩

theorem OConj.trans {O : Subgroup Y} {a b c : Y} (h₁ : OConj O a b) (h₂ : OConj O b c) :
    OConj O a c := by
  obtain ⟨o, ho, rfl⟩ := h₁
  obtain ⟨p, hp, rfl⟩ := h₂
  exact ⟨o * p, O.mul_mem ho hp, by group⟩

theorem OConj.conj {C O : Subgroup Y} (hOC : ∀ g ∈ C, ∀ o ∈ O, g * o * g⁻¹ ∈ O) {g : Y} (hg : g ∈ C)
    {a b : Y} (h : OConj O a b) : OConj O (g * a * g⁻¹) (g * b * g⁻¹) := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨g * o * g⁻¹, hOC g hg o ho, by group⟩

theorem OConj.of_sq_conj {C O : Subgroup Y} (hOC : ∀ g ∈ C, ∀ o ∈ O, g * o * g⁻¹ ∈ O) {e x₀ : Y}
    {k : ℕ} (hx : x₀ ∈ C) (hxk : x₀ ^ 3 ^ k = 1)
    (h : OConj O e (x₀ ^ 2 * e * (x₀ ^ 2)⁻¹)) : OConj O e (x₀ * e * x₀⁻¹) := by
  have key : ∀ m : ℕ, OConj O e (x₀ ^ (2 * m) * e * (x₀ ^ (2 * m))⁻¹) := by
    intro m
    induction m with
    | zero => simpa using OConj.refl O e
    | succ m ih =>
      have h1 := OConj.conj hOC (C.pow_mem hx (2 * m)) h
      have e1 : x₀ ^ (2 * m) * (x₀ ^ 2 * e * (x₀ ^ 2)⁻¹) * (x₀ ^ (2 * m))⁻¹ =
          x₀ ^ (2 * (m + 1)) * e * (x₀ ^ (2 * (m + 1)))⁻¹ := by
        rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
        group
      rw [e1] at h1
      exact ih.trans h1
  obtain ⟨r, hr⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have h2 := key (r + 1)
  have e2 : x₀ ^ (2 * (r + 1)) = x₀ := by
    rw [show 2 * (r + 1) = 3 ^ k + 1 by omega, pow_succ, hxk, one_mul]
  rwa [e2] at h2

theorem exists_pow_of_three_classes {C O : Subgroup Y} (hOC : ∀ g ∈ C, ∀ o ∈ O, g * o * g⁻¹ ∈ O)
    {e y x₀ : Y} {k : ℕ}
    (hcls : ∀ c ∈ C, ∃ i : ℕ, i < 3 ∧ OConj O (c * e * c⁻¹) (y ^ i * e * (y ^ i)⁻¹))
    (hx : x₀ ∈ C) (hxk : x₀ ^ 3 ^ k = 1) (hmove : ¬ OConj O (x₀ * e * x₀⁻¹) e) :
    ∀ c ∈ C, ∃ j : ℕ, j < 3 ∧ OConj O (c * e * c⁻¹) (x₀ ^ j * e * (x₀ ^ j)⁻¹) := by
  intro c hc
  have h01 : ¬ OConj O e (x₀ * e * x₀⁻¹) := fun h => hmove h.symm
  have h12 : ¬ OConj O (x₀ * e * x₀⁻¹) (x₀ ^ 2 * e * (x₀ ^ 2)⁻¹) := by
    intro h
    have := OConj.conj hOC (C.inv_mem hx) h
    apply h01
    have e1 : x₀⁻¹ * (x₀ * e * x₀⁻¹) * x₀⁻¹⁻¹ = e := by group
    have e2 : x₀⁻¹ * (x₀ ^ 2 * e * (x₀ ^ 2)⁻¹) * x₀⁻¹⁻¹ = x₀ * e * x₀⁻¹ := by group
    rw [e1, e2] at this
    exact this
  have h02 : ¬ OConj O e (x₀ ^ 2 * e * (x₀ ^ 2)⁻¹) := fun h => h01 (OConj.of_sq_conj hOC hx hxk h)
  obtain ⟨i₀, hi₀, hr₀⟩ := hcls 1 C.one_mem
  obtain ⟨i₁, hi₁, hr₁⟩ := hcls x₀ hx
  obtain ⟨i₂, hi₂, hr₂⟩ := hcls (x₀ ^ 2) (C.pow_mem hx 2)
  obtain ⟨i, hi, hr⟩ := hcls c hc
  have e0 : (1 : Y) * e * 1⁻¹ = e := by group
  rw [e0] at hr₀
  have same : ∀ {a b : Y} {p q : ℕ}, p = q →
      OConj O a (y ^ p * e * (y ^ p)⁻¹) → OConj O b (y ^ q * e * (y ^ q)⁻¹) → OConj O a b := by
    intro a b p q hpq ha hb
    subst hpq
    exact ha.trans hb.symm
  have n01 : i₀ ≠ i₁ := fun h => h01 (same h hr₀ hr₁)
  have n12 : i₁ ≠ i₂ := fun h => h12 (same h hr₁ hr₂)
  have n02 : i₀ ≠ i₂ := fun h => h02 (same h hr₀ hr₂)
  have hcases : i = i₀ ∨ i = i₁ ∨ i = i₂ := by omega
  rcases hcases with h | h | h
  · exact ⟨0, by norm_num, by rw [pow_zero, inv_one, one_mul, mul_one]; exact same h hr hr₀⟩
  · exact ⟨1, by norm_num, by rw [pow_one]; exact same h hr hr₁⟩
  · exact ⟨2, by norm_num, same h hr hr₂⟩

end Cls

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.AWM
