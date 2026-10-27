module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Field

public section

namespace CFSG.OddStandard.Seitz77

namespace Weights16

open CFSG.GH74.KGroups

section Criteria

variable {F : Type*} [Field F] (hF : Nat.card F = 16) {z : F} (hz : orderOf z = 15)

theorem lin_of_single {c : Fin 4 → F} {i₀ : Fin 4} (h : ∀ i, i ≠ i₀ → c i = 0) (x : F) :
    lin c x = c i₀ * x ^ 2 ^ (i₀ : ℕ) := by
  unfold lin
  rw [Finset.sum_eq_single i₀]
  · intro i _ hi
    simp [h i hi]
  · intro h'
    exact absurd (Finset.mem_univ i₀) h'

include hF hz

theorem additive_zero_of_weight {a b : ℕ} (hno : ∀ i : Fin 4, ¬ a * 2 ^ (i : ℕ) ≡ b [MOD 15])
    {f : F → F} (hf : ∀ x y, f (x + y) = f x + f y) (h : ∀ x, f (z ^ a * x) = z ^ b * f x) :
    ∀ x, f x = 0 := by
  obtain ⟨c, hc, hc'⟩ := additive_weight_field hF hz a b hf h
  have h0 : ∀ i, c i = 0 := fun i => by
    by_contra hi
    exact hno i (hc' i hi)
  intro x
  rw [hc, lin_def, h0 0, h0 1, h0 2, h0 3]
  simp

theorem additive_single_of_weight {a b : ℕ} {i₀ : Fin 4}
    (hs : ∀ i : Fin 4, a * 2 ^ (i : ℕ) ≡ b [MOD 15] → i = i₀)
    {f : F → F} (hf : ∀ x y, f (x + y) = f x + f y) (h : ∀ x, f (z ^ a * x) = z ^ b * f x) :
    ∃ c : F, ∀ x, f x = c * x ^ 2 ^ (i₀ : ℕ) := by
  obtain ⟨c, hc, hc'⟩ := additive_weight_field hF hz a b hf h
  refine ⟨c i₀, fun x => ?_⟩
  rw [hc, lin_of_single]
  intro i hi
  by_contra hne
  exact hi (hs i (hc' i hne))

theorem biadditive_zero_of_weight {a b e : ℕ}
    (hno : ∀ i j : Fin 4, ¬ a * 2 ^ (i : ℕ) + b * 2 ^ (j : ℕ) ≡ e [MOD 15])
    {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (h : ∀ x y, β (z ^ a * x) (z ^ b * y) = z ^ e * β x y) : ∀ x y, β x y = 0 := by
  obtain ⟨c, hc, hc'⟩ := biadditive_weight_field hF hz a b e hx hy h
  have h0 : c = fun _ _ => 0 := funext fun i => funext fun j => by
    by_contra hij
    exact hno i j (hc' i j hij)
  intro x y
  rw [hc, h0]
  exact bilin_zero x y

theorem biadditive_single_of_weight {a b e : ℕ} {i₀ j₀ : Fin 4}
    (hs : ∀ i j : Fin 4, a * 2 ^ (i : ℕ) + b * 2 ^ (j : ℕ) ≡ e [MOD 15] → i = i₀ ∧ j = j₀)
    {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (h : ∀ x y, β (z ^ a * x) (z ^ b * y) = z ^ e * β x y) :
    ∃ c : F, ∀ x y, β x y = c * x ^ 2 ^ (i₀ : ℕ) * y ^ 2 ^ (j₀ : ℕ) := by
  obtain ⟨c, hc, hc'⟩ := biadditive_weight_field hF hz a b e hx hy h
  refine ⟨c i₀ j₀, fun x y => ?_⟩
  rw [hc, bilin_of_single (i₀ := i₀) (j₀ := j₀)]
  intro i j hij
  by_contra hne
  have := hs i j (hc' i j hne)
  rcases hij with hij | hij
  · exact hij this.1
  · exact hij this.2

end Criteria

section Table

variable {F : Type*} [Field F] (hF : Nat.card F = 16) {z : F} (hz : orderOf z = 15)
include hF hz

theorem additive_Lambda_W0 {f : F → F} (hf : ∀ x y, f (x + y) = f x + f y)
    (h : ∀ x, f (z ^ 14 * x) = z * f x) : ∀ x, f x = 0 :=
  additive_zero_of_weight hF hz (a := 14) (b := 1) (by decide) hf (fun x => by
    rw [pow_one]; exact h x)

theorem additive_W0_Lambda {f : F → F} (hf : ∀ x y, f (x + y) = f x + f y)
    (h : ∀ x, f (z * x) = z ^ 14 * f x) : ∀ x, f x = 0 :=
  additive_zero_of_weight hF hz (a := 1) (b := 14) (by decide) hf (fun x => by
    rw [pow_one]; exact h x)

theorem biadditive_U_Lambda_W0 {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (h : ∀ x y, β (z ^ 2 * x) (z ^ 14 * y) = z * β x y) :
    ∃ c : F, ∀ x y, β x y = c * x * y := by
  obtain ⟨c, hc⟩ := biadditive_single_of_weight hF hz (a := 2) (b := 14) (e := 1) (i₀ := 0)
    (j₀ := 0) (by decide) hx hy (fun x y => by rw [pow_one]; exact h x y)
  exact ⟨c, fun x y => by simpa using hc x y⟩

theorem biadditive_U_U_Lambda {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (h : ∀ x y, β (z ^ 2 * x) (z ^ 2 * y) = z ^ 14 * β x y) : ∀ x y, β x y = 0 :=
  biadditive_zero_of_weight hF hz (a := 2) (b := 2) (e := 14) (by decide) hx hy h

theorem biadditive_U_W0_Lambda {β : F → F → F} (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (h : ∀ x y, β (z ^ 2 * x) (z * y) = z ^ 14 * β x y) : ∀ x y, β x y = 0 :=
  biadditive_zero_of_weight hF hz (a := 2) (b := 1) (e := 14) (by decide) hx hy (fun x y => by
    rw [pow_one]; exact h x y)

end Table

end Weights16

end CFSG.OddStandard.Seitz77
