module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Weights16Core
public import Mathlib.RingTheory.PiTensorProduct

public section

namespace CFSG.OddStandard.Seitz77

namespace Weights16

open CFSG.GH74.KGroups
open scoped Matrix

@[expose] def bilin {R : Type*} [CommSemiring R] (c : Fin 4 → Fin 4 → R) (x y : R) : R :=
  lin (fun j => lin (fun i => c i j) x) y

theorem bilin_zero {R : Type*} [CommSemiring R] (x y : R) :
    bilin (fun _ _ => (0 : R)) x y = 0 := by
  simp [bilin, lin]

theorem bilin_of_single {R : Type*} [CommSemiring R] {c : Fin 4 → Fin 4 → R} {i₀ j₀ : Fin 4}
    (h : ∀ i j : Fin 4, (i ≠ i₀ ∨ j ≠ j₀) → c i j = 0) (x y : R) :
    bilin c x y = c i₀ j₀ * x ^ 2 ^ (i₀ : ℕ) * y ^ 2 ^ (j₀ : ℕ) := by
  have h1 : ∀ j : Fin 4, lin (fun i => c i j) x =
      if j = j₀ then c i₀ j₀ * x ^ 2 ^ (i₀ : ℕ) else 0 := by
    intro j
    unfold lin
    split_ifs with hj
    · subst hj
      rw [Finset.sum_eq_single i₀]
      · intro i _ hi
        simp [h i j (Or.inl hi)]
      · intro h'
        exact absurd (Finset.mem_univ i₀) h'
    · exact Finset.sum_eq_zero fun i _ => by simp [h i j (Or.inr hj)]
  unfold bilin
  simp only [h1]
  unfold lin
  rw [Finset.sum_eq_single j₀]
  · simp [mul_assoc]
  · intro j _ hj
    simp [hj]
  · intro h'
    exact absurd (Finset.mem_univ j₀) h'

theorem biadditive_weight {r : GF16} (hr : orderOf r = 15) (a b e : ℕ) {β : GF16 → GF16 → GF16}
    (hx : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (hy : ∀ x y y', β x (y + y') = β x y + β x y')
    (hβ : ∀ x y, β (r ^ a * x) (r ^ b * y) = r ^ e * β x y) :
    ∃ c : Fin 4 → Fin 4 → GF16, (∀ x y, β x y = bilin c x y) ∧
      ∀ i j : Fin 4, c i j ≠ 0 → a * 2 ^ (i : ℕ) + b * 2 ^ (j : ℕ) ≡ e [MOD 15] := by
  set d : GF16 → Fin 4 → GF16 :=
    fun x => mooreInv *ᵥ fun k : Fin 4 => β x (zeta ^ (k : ℕ)) with hd
  have hβd : ∀ x y, β x y = lin (d x) y := fun x y =>
    eq_lin_of_additive (f := fun y => β x y) (hy x) y
  have hdadd : ∀ j x x', d (x + x') j = d x j + d x' j := by
    intro j x x'
    simp only [hd, Matrix.mulVec, dotProduct, hx, mul_add, Finset.sum_add_distrib]
  set e' : Fin 4 → Fin 4 → GF16 :=
    fun j => mooreInv *ᵥ fun i : Fin 4 => d (zeta ^ (i : ℕ)) j with he'
  have hde : ∀ j x, d x j = lin (e' j) x := fun j x =>
    eq_lin_of_additive (f := fun x => d x j) (hdadd j) x
  refine ⟨fun i j => e' j i, fun x y => ?_, fun i j hij => ?_⟩
  · rw [hβd]
    simp only [bilin]
    congr 1
    funext j
    exact hde j x
  ·
    have h1 : ∀ x j, d (r ^ a * x) j * r ^ (b * 2 ^ (j : ℕ)) = r ^ e * d x j := by
      intro x
      have h : (fun j => d (r ^ a * x) j * (r ^ b) ^ 2 ^ (j : ℕ) - r ^ e * d x j) = 0 := by
        apply lin_unique
        intro y
        have := hβ x y
        rw [hβd, hβd, lin_scale, lin_mul_left] at this
        rw [← lin_sub, this, sub_self]
      intro j
      have := sub_eq_zero.1 (congrFun h j)
      rwa [← pow_mul] at this
    have h2 : (fun i => e' j i * ((r ^ a) ^ 2 ^ (i : ℕ) * r ^ (b * 2 ^ (j : ℕ)) - r ^ e)) = 0 := by
      apply lin_unique
      intro x
      have := h1 x j
      rw [hde, hde, lin_scale, lin_mul_right, lin_mul_left, ← sub_eq_zero, lin_sub] at this
      rw [← this]
      congr 1
      funext i
      ring
    have h3 : e' j i * ((r ^ a) ^ 2 ^ (i : ℕ) * r ^ (b * 2 ^ (j : ℕ)) - r ^ e) = 0 :=
      congrFun h2 i
    have h4 : (r ^ a) ^ 2 ^ (i : ℕ) * r ^ (b * 2 ^ (j : ℕ)) = r ^ e := by
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd h hij
      · exact sub_eq_zero.1 h
    rw [← pow_mul, ← pow_add] at h4
    have hfin : IsOfFinOrder r := orderOf_pos_iff.1 (by rw [hr]; norm_num)
    have := hfin.pow_eq_pow_iff_modEq.1 h4
    rwa [hr] at this

end Weights16

end CFSG.OddStandard.Seitz77
