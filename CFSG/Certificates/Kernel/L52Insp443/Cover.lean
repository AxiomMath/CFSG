module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.KC.L52I

variable {G : Type*} [Group G] [Finite G] {s : Set G} (hs : Subgroup.closure s = ⊤)
  (S : Subgroup G) {m : ℕ} (t : Fin m → G)

include hs in
theorem exists_coset_of_cover (hcov : ∀ x ∈ s, ∀ k, ∃ j, (t j)⁻¹ * (x * t k) ∈ S)
    (h0 : ∃ k, t k ∈ S) (g : G) : ∃ k, (t k)⁻¹ * g ∈ S := by
  have step : ∀ x ∈ s, ∀ y : G, (∃ k, (t k)⁻¹ * y ∈ S) → ∃ k, (t k)⁻¹ * (x * y) ∈ S := by
    rintro x hx y ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hcov x hx k
    refine ⟨j, ?_⟩
    have e : (t j)⁻¹ * (x * y) = ((t j)⁻¹ * (x * t k)) * ((t k)⁻¹ * y) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact S.mul_mem hj hk
  have stepPow : ∀ x ∈ s, ∀ n : ℕ, ∀ y : G, (∃ k, (t k)⁻¹ * y ∈ S) →
      ∃ k, (t k)⁻¹ * (x ^ n * y) ∈ S := by
    intro x hx n
    induction n with
    | zero =>
      intro y hy
      rw [pow_zero, one_mul]
      exact hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact step x hx _ (ih y hy)
  have hg : g ∈ Subgroup.closure s := by
    rw [hs]
    exact Subgroup.mem_top g
  induction hg using Subgroup.closure_induction_left with
  | one =>
    obtain ⟨k, hk⟩ := h0
    exact ⟨k, by rw [mul_one]; exact S.inv_mem hk⟩
  | mul_left x hx y _ ih => exact step x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    have hc : 0 < Nat.card G := Nat.card_pos
    have e1 : x ^ (Nat.card G - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']
    rw [← eq_inv_of_mul_eq_one_left e1]
    exact stepPow x hx _ y ih

theorem coset_unique {α : Type*} (key : G → α) (hkey : ∀ g, ∀ x ∈ S, key (g * x) = key g)
    (hinj : Function.Injective fun k => key (t k)) {g : G} {j k : Fin m}
    (hj : (t j)⁻¹ * g ∈ S) (hk : (t k)⁻¹ * g ∈ S) : j = k := by
  apply hinj
  change key (t j) = key (t k)
  rw [← hkey (t j) _ hj, ← hkey (t k) _ hk, mul_inv_cancel_left, mul_inv_cancel_left]

include hs in
theorem exists_schreier (P : Subgroup G)
    (hcov : ∀ x ∈ s, ∀ k, ∃ j, (t j)⁻¹ * (x * t k) ∈ S ∧ (t j)⁻¹ * (x * t k) ∈ P) (g : G) (k : Fin m) :
    ∃ j, (t j)⁻¹ * (g * t k) ∈ S ∧ (t j)⁻¹ * (g * t k) ∈ P := by
  have step : ∀ x ∈ s, ∀ y : G, (∀ k, ∃ j, (t j)⁻¹ * (y * t k) ∈ S ∧ (t j)⁻¹ * (y * t k) ∈ P) →
      ∀ k, ∃ j, (t j)⁻¹ * (x * y * t k) ∈ S ∧ (t j)⁻¹ * (x * y * t k) ∈ P := by
    intro x hx y hy k
    obtain ⟨j, hj1, hj2⟩ := hy k
    obtain ⟨i, hi1, hi2⟩ := hcov x hx j
    refine ⟨i, ?_⟩
    have e : (t i)⁻¹ * (x * y * t k) = ((t i)⁻¹ * (x * t j)) * ((t j)⁻¹ * (y * t k)) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact ⟨S.mul_mem hi1 hj1, P.mul_mem hi2 hj2⟩
  have stepPow : ∀ x ∈ s, ∀ n : ℕ, ∀ y : G,
      (∀ k, ∃ j, (t j)⁻¹ * (y * t k) ∈ S ∧ (t j)⁻¹ * (y * t k) ∈ P) →
      ∀ k, ∃ j, (t j)⁻¹ * (x ^ n * y * t k) ∈ S ∧ (t j)⁻¹ * (x ^ n * y * t k) ∈ P := by
    intro x hx n
    induction n with
    | zero =>
      intro y hy
      simpa only [pow_zero, one_mul] using hy
    | succ n ih =>
      intro y hy
      have e : x ^ (n + 1) * y = x * (x ^ n * y) := by rw [pow_succ', mul_assoc]
      rw [e]
      exact step x hx _ (ih y hy)
  have hg : g ∈ Subgroup.closure s := by
    rw [hs]
    exact Subgroup.mem_top g
  revert k
  induction hg using Subgroup.closure_induction_left with
  | one =>
    intro k
    exact ⟨k, by rw [one_mul, inv_mul_cancel]; exact ⟨S.one_mem, P.one_mem⟩⟩
  | mul_left x hx y _ ih => exact step x hx y ih
  | inv_mul_cancel x hx y _ ih =>
    have hc : 0 < Nat.card G := Nat.card_pos
    have e1 : x ^ (Nat.card G - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']
    rw [← eq_inv_of_mul_eq_one_left e1]
    exact stepPow x hx _ y ih

include hs in
theorem le_of_schreier {α : Type*} (key : G → α) (hkey : ∀ g, ∀ x ∈ S, key (g * x) = key g)
    (hinj : Function.Injective fun k => key (t k)) (P : Subgroup G)
    (hcov : ∀ x ∈ s, ∀ k, ∃ j, (t j)⁻¹ * (x * t k) ∈ S ∧ (t j)⁻¹ * (x * t k) ∈ P)
    {k₀ : Fin m} (h₀ : t k₀ = 1) : S ≤ P := by
  intro g hg
  obtain ⟨j, hj1, hj2⟩ := exists_schreier hs S t P hcov g k₀
  rw [h₀, mul_one] at hj1 hj2
  have h1 : (t k₀)⁻¹ * g ∈ S := by rw [h₀, inv_one, one_mul]; exact hg
  have hjk := coset_unique S t key hkey hinj hj1 h1
  rw [hjk, h₀, inv_one, one_mul] at hj2
  exact hj2

include hs in
theorem card_eq_mul_of_cover {α : Type*} (key : G → α)
    (hkey : ∀ g, ∀ x ∈ S, key (g * x) = key g) (hinj : Function.Injective fun k => key (t k))
    (hcov : ∀ x ∈ s, ∀ k, ∃ j, (t j)⁻¹ * (x * t k) ∈ S) (h0 : ∃ k, t k ∈ S) :
    Nat.card G = m * Nat.card S := by
  classical
  have hex := exists_coset_of_cover hs S t hcov h0
  let f : Fin m × S → G := fun p => t p.1 * p.2
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨j, x⟩ ⟨k, y⟩ e
      have e' : t j * x = t k * y := e
      have hj : (t j)⁻¹ * (t j * x) ∈ S := by rw [inv_mul_cancel_left]; exact x.2
      have hk : (t k)⁻¹ * (t j * x) ∈ S := by rw [e', inv_mul_cancel_left]; exact y.2
      have hjk := coset_unique S t key hkey hinj hj hk
      subst hjk
      have hxy : (x : G) = y := mul_left_cancel e'
      exact Prod.ext rfl (Subtype.ext hxy)
    · intro g
      obtain ⟨k, hk⟩ := hex g
      exact ⟨(k, ⟨_, hk⟩), by change t k * ((t k)⁻¹ * g) = g; rw [mul_inv_cancel_left]⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end CFSG.KC.L52I

end
