module

public import CFSG.LargeExtraspecial.Asc611OutC

public section

namespace CFSG.LargeExtraspecial.Asc611

open Subgroup Matrix CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

namespace SemiInv

variable {S : (Fin m → K) → Fin m → K} (hS : SemiInv S)
include hS

theorem smul_fix {c : K} (hc : c = 0 ∨ c = 1) {x : Fin m → K} (hx : S x = x) :
    S (c • x) = c • x := by
  rw [hS.smul, hx, (frob_eq_self_iff c).mpr hc]

theorem ite_fix (b : Bool) {x : Fin m → K} (hx : S x = x) :
    S (if b then x else 0) = if b then x else 0 := by
  cases b
  · exact hS.zero
  · exact hx

theorem exists_decomp_P {x₀ v₁ y : Fin m → K} (hx₀S : S x₀ = x₀) (hx₀ : herm frob x₀ x₀ = 1)
    (hv₁S : S v₁ = v₁) (hv₁ : herm frob v₁ v₁ = 0) (hyS : S y = y)
    (hv₁y : herm frob v₁ y = 1) {x : Fin m → K} (hxS : S x = x) :
    ∃ p : Fin m → K, (S p = p ∧ herm frob p p = 0 ∧ herm frob p y = 0) ∧ ∃ a b : Bool,
      x = p + (if a then x₀ else 0) + (if b then v₁ else 0) := by
  obtain ⟨a, x', hx'S, hx'iso, hx'eq⟩ : ∃ a : Bool, ∃ x' : Fin m → K, S x' = x' ∧
      herm frob x' x' = 0 ∧ x = x' + (if a then x₀ else 0) := by
    rcases herm_self_eq_zero_or_one x with h0 | h1
    · exact ⟨false, x, hxS, h0, by simp⟩
    · refine ⟨true, x + x₀, by rw [hS.add, hxS, hx₀S], ?_, ?_⟩
      · rw [hS.herm_add_add hxS hx₀S, h1, hx₀, add_self_K]
      · simp only [↓reduceIte]
        linear_combination (norm := module) -(two_eq_zero • x₀)
  obtain ⟨b, p, hpS, hpiso, hpy, hpeq⟩ : ∃ b : Bool, ∃ p : Fin m → K, S p = p ∧
      herm frob p p = 0 ∧ herm frob p y = 0 ∧ x' = p + (if b then v₁ else 0) := by
    rcases hS.herm_fix hx'S hyS with h0 | h1
    · exact ⟨false, x', hx'S, hx'iso, h0, by simp⟩
    · refine ⟨true, x' + v₁, by rw [hS.add, hx'S, hv₁S], ?_, ?_, ?_⟩
      · rw [hS.herm_add_add hx'S hv₁S, hx'iso, hv₁, add_zero]
      · rw [herm_add_left, h1, hv₁y, add_self_K]
      · simp only [↓reduceIte]
        linear_combination (norm := module) -(two_eq_zero • v₁)
  refine ⟨p, ⟨hpS, hpiso, hpy⟩, a, b, ?_⟩
  rw [hx'eq, hpeq]
  abel

theorem exists_pair (hm : 5 ≤ m) {x₀ v₁ y : Fin m → K} (hx₀S : S x₀ = x₀)
    (hx₀ : herm frob x₀ x₀ = 1) (hv₁S : S v₁ = v₁) (hv₁ : herm frob v₁ v₁ = 0)
    (hyS : S y = y) (hv₁y : herm frob v₁ y = 1) :
    ∃ s s' : Fin m → K, S s = s ∧ S s' = s' ∧ herm frob s s = 0 ∧ herm frob s' s' = 0 ∧
      herm frob s y = 0 ∧ herm frob s' y = 0 ∧ herm frob s s' = 1 := by
  classical
  by_contra hcon
  have hP : ∀ s s' : Fin m → K, S s = s → S s' = s' → herm frob s s = 0 →
      herm frob s' s' = 0 → herm frob s y = 0 → herm frob s' y = 0 → herm frob s s' = 0 := by
    intro s s' hs hs' h1 h2 h3 h4
    rcases hS.herm_fix hs hs' with h0 | h1'
    · exact h0
    · exact absurd ⟨s, s', hs, hs', h1, h2, h3, h4, h1'⟩ hcon
  have : Finite K := AS35U.hF.finite
  let V0 := {x : Fin m → K // S x = x}
  let P := {x : Fin m → K // S x = x ∧ herm frob x x = 0 ∧ herm frob x y = 0}
  have hPinj : Function.Injective (fun p : P =>
      (decide (herm frob (p : Fin m → K) x₀ = 1), decide (herm frob (p : Fin m → K) v₁ = 1))) := by
    rintro ⟨p, hpS, hpp0, hpy⟩ ⟨p', hp'S, hp'p0, hp'y⟩ hpp
    simp only [Prod.mk.injEq, decide_eq_decide] at hpp
    have e1 : herm frob p x₀ = herm frob p' x₀ := by
      rcases hS.herm_fix hpS hx₀S with h | h <;> rcases hS.herm_fix hp'S hx₀S with h' | h'
      · rw [h, h']
      · exact absurd (hpp.1.mpr h') (by rw [h]; exact zero_ne_one)
      · exact absurd (hpp.1.mp h) (by rw [h']; exact zero_ne_one)
      · rw [h, h']
    have e2 : herm frob p v₁ = herm frob p' v₁ := by
      rcases hS.herm_fix hpS hv₁S with h | h <;> rcases hS.herm_fix hp'S hv₁S with h' | h'
      · rw [h, h']
      · exact absurd (hpp.2.mpr h') (by rw [h]; exact zero_ne_one)
      · exact absurd (hpp.2.mp h) (by rw [h']; exact zero_ne_one)
      · rw [h, h']
    set d := p + p' with hd
    have hdS : S d = d := by rw [hd, hS.add, hpS, hp'S]
    have hdiso : herm frob d d = 0 := by rw [hd, hS.herm_add_add hpS hp'S, hpp0, hp'p0, add_zero]
    have hdy : herm frob d y = 0 := by rw [hd, herm_add_left, hpy, hp'y, add_zero]
    have hdx₀ : herm frob d x₀ = 0 := by rw [hd, herm_add_left, e1, add_self_K]
    have hdv₁ : herm frob d v₁ = 0 := by rw [hd, herm_add_left, e2, add_self_K]
    have hd0 : d = 0 := hS.eq_zero_of_herm fun x hxS => by
      obtain ⟨q, ⟨hqS, hqiso, hqy⟩, a, b, rfl⟩ :=
        hS.exists_decomp_P hx₀S hx₀ hv₁S hv₁ hyS hv₁y hxS
      have hfix : S (q + (if a then x₀ else 0) + (if b then v₁ else 0)) =
          q + (if a then x₀ else 0) + (if b then v₁ else 0) := by
        rw [hS.add, hS.add, hqS, hS.ite_fix a hx₀S, hS.ite_fix b hv₁S]
      rw [hS.herm_symm hdS hfix, herm_add_right, herm_add_right,
        hP d q hdS hqS hdiso hqiso hdy hqy]
      cases a <;> cases b <;>
        simp only [Bool.false_eq_true, ↓reduceIte, herm_zero_right, add_zero, hdx₀, hdv₁]
    have : p' = p := by
      calc p' = p + d := by rw [hd]; linear_combination (norm := module) -(two_eq_zero • p)
        _ = p := by rw [hd0, add_zero]
    exact Subtype.ext this.symm
  have hPcard : Nat.card P ≤ 4 := by
    have h1 := Nat.card_le_card_of_injective _ hPinj
    simpa using h1
  have : Finite P := Subtype.finite
  have : Finite V0 := Subtype.finite
  have hV0surj : Function.Surjective (fun t : P × Bool × Bool =>
      (⟨(t.1 : Fin m → K) + (if t.2.1 then x₀ else 0) + (if t.2.2 then v₁ else 0), by
        rw [hS.add, hS.add, t.1.2.1, hS.ite_fix _ hx₀S, hS.ite_fix _ hv₁S]⟩ : V0)) := by
    rintro ⟨x, hxS⟩
    obtain ⟨q, hq, a, b, rfl⟩ := hS.exists_decomp_P hx₀S hx₀ hv₁S hv₁ hyS hv₁y hxS
    exact ⟨(⟨q, hq⟩, a, b), rfl⟩
  have hV0card : Nat.card V0 ≤ 16 := by
    change Nat.card {x : Fin m → K // S x = x} ≤ 16
    have h1 := Nat.card_le_card_of_surjective _ hV0surj
    have hB : Nat.card Bool = 2 := by simp
    rw [Nat.card_prod, Nat.card_prod, hB] at h1
    omega
  have hVsurj : Function.Surjective (fun t : V0 × V0 => frob ω • (t.1 : Fin m → K) + t.2) := by
    intro x
    exact ⟨(⟨x + S x, hS.fix_add_self x⟩, ⟨ω • x + S (ω • x), hS.fix_add_self _⟩),
      (hS.decomp x).symm⟩
  have hVcard := Nat.card_le_card_of_surjective _ hVsurj
  rw [Nat.card_prod, Nat.card_fun, card_K, Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin] at hVcard
  have h1 : 4 ^ 5 ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : Nat.card V0 * Nat.card V0 ≤ 16 * 16 := Nat.mul_le_mul hV0card hV0card
  norm_num at hVcard h1
  omega


end SemiInv

end CFSG.LargeExtraspecial.Asc611
