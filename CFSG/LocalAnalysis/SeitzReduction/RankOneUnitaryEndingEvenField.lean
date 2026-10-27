module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.SeitzReduction.RankOne

namespace NormIsometry

variable {E : Type*} [Field E] [CharP E 2] (σ : E →+* E)

theorem eq_of_add_eq_zero' {a b : E} (h : a + b = 0) : b = a := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  linear_combination h - a * h2

omit [CharP E 2] in
theorem norm_add (a b : E) :
    (a + b) * σ (a + b) = a * σ a + b * σ b + (a * σ b + σ a * b) := by
  rw [map_add]
  ring

omit [CharP E 2] in
theorem polar_apply {α : E → E} (hadd : ∀ a b, α (a + b) = α a + α b)
    (hN : ∀ a, α a * σ (α a) = a * σ a) (a b : E) :
    α a * σ (α b) + σ (α a) * α b = a * σ b + σ a * b := by
  have h1 := hN (a + b)
  rw [hadd, norm_add, norm_add, hN a, hN b] at h1
  linear_combination h1

theorem eq_mul_of_polar_eq_zero (hσσ : ∀ x, σ (σ x) = x) {c y : E} (hc : c ≠ 0)
    (h : c * σ y + σ c * y = 0) : σ (y / c) = y / c ∧ y = y / c * c := by
  have hσc : σ c ≠ 0 := by
    intro h0
    apply hc
    rw [← hσσ c, h0, map_zero]
  refine ⟨?_, by field_simp⟩
  have h' : c * σ y = σ c * y := (eq_of_add_eq_zero' h).symm
  rw [map_div₀, div_eq_div_iff hσc hc]
  linear_combination h'

omit [CharP E 2] in
theorem norm_mul_of_fixed {l : E} (hl : σ l = l) (c : E) :
    l * c * σ (l * c) = l * l * (c * σ c) := by
  rw [map_mul, hl]
  ring

theorem eq_or_eq_reflection (hσσ : ∀ x, σ (σ x) = x) {α : E → E}
    (hadd : ∀ a b, α (a + b) = α a + α b) (hN : ∀ a, α a * σ (α a) = a * σ a) {c : E}
    (hc : c ≠ 0) (hαc : α c = c) :
    (∀ x, α x = x) ∨ ∀ x, α x = x + (x * σ c + σ x * c) / (c * σ c) * c := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hσc : σ c ≠ 0 := by
    intro h0
    apply hc
    rw [← hσσ c, h0, map_zero]
  have hNc : c * σ c ≠ 0 := mul_ne_zero hc hσc
  have hB := polar_apply σ hadd hN
  set lam : E → E := fun x => (α x + x) / c with hlam
  have hperp : ∀ x, c * σ (α x + x) + σ c * (α x + x) = 0 := by
    intro x
    have h1 := hB c x
    rw [hαc] at h1
    rw [map_add]
    linear_combination h1 + (c * σ x + σ c * x) * h2
  have hlamF : ∀ x, σ (lam x) = lam x := fun x =>
    (eq_mul_of_polar_eq_zero σ hσσ hc (hperp x)).1
  have hαx : ∀ x, α x = x + lam x * c := by
    intro x
    have h1 : α x + x = lam x * c := by rw [hlam]; field_simp
    linear_combination h1 - x * h2
  have hquad : ∀ x, lam x * (lam x * (c * σ c) + (x * σ c + σ x * c)) = 0 := by
    intro x
    have h1 := hN x
    rw [hαx x, norm_add, norm_mul_of_fixed σ (hlamF x), map_mul, hlamF x] at h1
    linear_combination h1
  set lam₀ : E → E := fun x => (x * σ c + σ x * c) / (c * σ c) with hlam₀
  have hcases : ∀ x, lam x = 0 ∨ lam x = lam₀ x := by
    intro x
    rcases mul_eq_zero.mp (hquad x) with h | h
    · exact Or.inl h
    · right
      rw [hlam₀, eq_div_iff hNc]
      linear_combination h - (x * σ c + σ x * c) * h2
  have hlamadd : ∀ a b, lam (a + b) = lam a + lam b := by
    intro a b
    simp only [hlam, hadd]
    ring
  have hlam₀add : ∀ a b, lam₀ (a + b) = lam₀ a + lam₀ b := by
    intro a b
    simp only [hlam₀, map_add]
    ring
  by_cases hall : ∀ x, lam x = 0
  · left
    intro x
    rw [hαx x, hall x, zero_mul, add_zero]
  · right
    push Not at hall
    obtain ⟨x₁, hx₁⟩ := hall
    have hx₁' : lam x₁ = lam₀ x₁ := (hcases x₁).resolve_left hx₁
    have hall₀ : ∀ x, lam x = lam₀ x := by
      intro x
      by_contra hx
      have hx0 : lam x = 0 := (hcases x).resolve_right hx
      have hx0' : lam₀ x ≠ 0 := by
        intro h0
        exact hx (by rw [hx0, h0])
      rcases hcases (x₁ + x) with h | h
      · rw [hlamadd, hx0, add_zero] at h
        exact hx₁ h
      · rw [hlamadd, hlam₀add, hx0, add_zero, hx₁'] at h
        apply hx0'
        linear_combination -h
    intro x
    rw [hαx x, hall₀ x]

theorem fixed_mem_line (hσσ : ∀ x, σ (σ x) = x) {α : E → E}
    (hadd : ∀ a b, α (a + b) = α a + α b) (hN : ∀ a, α a * σ (α a) = a * σ a)
    (hne : ∃ x, α x ≠ x) {c : E} (hc : c ≠ 0) (hαc : α c = c) {x : E} (hx : α x = x) :
    σ (x / c) = x / c ∧ x = x / c * c := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hσc : σ c ≠ 0 := by
    intro h0
    apply hc
    rw [← hσσ c, h0, map_zero]
  have hNc : c * σ c ≠ 0 := mul_ne_zero hc hσc
  rcases eq_or_eq_reflection σ hσσ hadd hN hc hαc with h | h
  · obtain ⟨y, hy⟩ := hne
    exact absurd (h y) hy
  · have h1 := h x
    rw [hx] at h1
    have h3 : (x * σ c + σ x * c) / (c * σ c) * c = 0 := by linear_combination -h1
    have h4 : x * σ c + σ x * c = 0 := by
      rcases mul_eq_zero.mp h3 with h5 | h5
      · rcases div_eq_zero_iff.mp h5 with h6 | h6
        · exact h6
        · exact absurd h6 hNc
      · exact absurd h5 hc
    refine eq_mul_of_polar_eq_zero σ hσσ hc ?_
    linear_combination h4

theorem card_fixed_le [Finite E] (hσσ : ∀ x, σ (σ x) = x) {α : E → E}
    (hadd : ∀ a b, α (a + b) = α a + α b) (hN : ∀ a, α a * σ (α a) = a * σ a)
    (hne : ∃ x, α x ≠ x) : Nat.card {x : E // α x = x} ≤ Nat.card {x : E // σ x = x} := by
  have hα0 : α 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linear_combination -h
  by_cases hfix : ∃ c, c ≠ 0 ∧ α c = c
  · obtain ⟨c, hc, hαc⟩ := hfix
    let f : {x : E // α x = x} → {x : E // σ x = x} := fun x =>
      ⟨x.1 / c, (fixed_mem_line σ hσσ hadd hN hne hc hαc x.2).1⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => Subtype.ext ?_
    have h1 : x.1 / c = y.1 / c := congrArg Subtype.val hxy
    rw [(fixed_mem_line σ hσσ hadd hN hne hc hαc x.2).2,
      (fixed_mem_line σ hσσ hadd hN hne hc hαc y.2).2, h1]
  · push Not at hfix
    let f : {x : E // α x = x} → {x : E // σ x = x} := fun _ => ⟨0, map_zero σ⟩
    refine Nat.card_le_card_of_injective f fun x y _ => Subtype.ext ?_
    have hx : x.1 = 0 := by
      by_contra h
      exact hfix x.1 h x.2
    have hy : y.1 = 0 := by
      by_contra h
      exact hfix y.1 h y.2
    rw [hx, hy]

theorem exists_apply_eq_add (hσσ : ∀ x, σ (σ x) = x) {ω : E} (hω : σ ω ≠ ω) {α : E → E}
    (hadd : ∀ a b, α (a + b) = α a + α b) (hN : ∀ a, α a * σ (α a) = a * σ a)
    (hne : ∃ x, α x ≠ x) {c : E} (hc : c ≠ 0) (hαc : α c = c) : ∃ x, α x = x + c := by
  have hσc : σ c ≠ 0 := by
    intro h0
    apply hc
    rw [← hσσ c, h0, map_zero]
  have hNc : c * σ c ≠ 0 := mul_ne_zero hc hσc
  have hτ : ω + σ ω ≠ 0 := fun h => hω (eq_of_add_eq_zero' h)
  have hστ : σ (ω + σ ω) = ω + σ ω := by rw [map_add, hσσ, add_comm]
  rcases eq_or_eq_reflection σ hσσ hadd hN hc hαc with h | h
  · obtain ⟨y, hy⟩ := hne
    exact absurd (h y) hy
  · refine ⟨ω / (ω + σ ω) * c, ?_⟩
    rw [h]
    congr 1
    have hB : ω / (ω + σ ω) * c * σ c + σ (ω / (ω + σ ω) * c) * c = c * σ c := by
      rw [map_mul, map_div₀, hστ]
      field_simp
    rw [hB, div_self hNc, one_mul]

theorem eq_of_fixes_image (hσσ : ∀ x, σ (σ x) = x) {ω : E} (hω : σ ω ≠ ω) {α α' : E → E}
    (hadd : ∀ a b, α (a + b) = α a + α b) (hadd' : ∀ a b, α' (a + b) = α' a + α' b)
    (hN : ∀ a, α a * σ (α a) = a * σ a) (hN' : ∀ a, α' a * σ (α' a) = a * σ a)
    (hαα : ∀ x, α (α x) = x) (hfix : ∀ x, α' (α x + x) = α x + x)
    (hne : ∃ x, α x ≠ x) (hne' : ∃ x, α' x ≠ x) (x : E) : α x = α' x := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, hb⟩ := hne
  set c := b + α b with hcdef
  have hc : c ≠ 0 := fun h => hb (eq_of_add_eq_zero' h)
  have hαc : α c = c := by rw [hcdef, hadd, hαα, add_comm]
  obtain ⟨x₀, hx₀⟩ := exists_apply_eq_add σ hσσ hω hadd hN ⟨b, hb⟩ hc hαc
  have hα'c : α' c = c := by
    have h1 := hfix x₀
    rw [hx₀] at h1
    have e : x₀ + c + x₀ = c := by linear_combination x₀ * h2
    rwa [e] at h1
  rcases eq_or_eq_reflection σ hσσ hadd hN hc hαc with h | h
  · exact absurd (h b) hb
  · rcases eq_or_eq_reflection σ hσσ hadd' hN' hc hα'c with h' | h'
    · obtain ⟨y, hy⟩ := hne'
      exact absurd (h' y) hy
    · rw [h x, h' x]

end NormIsometry

end CFSG.SeitzReduction.RankOne
