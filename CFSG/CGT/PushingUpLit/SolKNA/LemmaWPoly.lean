module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open Polynomial

section ExpPoly

variable {K : Type*} [Field K]

@[expose] noncomputable def expPoly (k : ℕ) (d : Fin k → K) (f : Fin k → ℕ) : K[X] :=
  ∑ l : Fin k, C (d l) * X ^ f l

theorem expPoly_coeff {k : ℕ} (d : Fin k → K) (f : Fin k → ℕ) (n : ℕ) :
    (expPoly k d f).coeff n = ∑ l : Fin k, if n = f l then d l else 0 := by
  classical
  simp only [expPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : n = f l <;> simp [h]

theorem eval_expPoly {k : ℕ} (d : Fin k → K) (f : Fin k → ℕ) (t : K) :
    (expPoly k d f).eval t = ∑ l : Fin k, d l * t ^ f l := by
  simp [expPoly, eval_finsetSum]

theorem degree_expPoly_lt {k : ℕ} (d : Fin k → K) (f : Fin k → ℕ) {m : ℕ} (hf : ∀ l, f l < m) :
    (expPoly k d f).degree < m := by
  rw [degree_lt_iff_coeff_zero]
  intro n hn
  rw [expPoly_coeff]
  refine Finset.sum_eq_zero fun l _ => ?_
  have := hf l
  simp [show n ≠ f l by omega]

theorem eq_of_eval_expPoly {k : ℕ} (d : Fin k → K) (f g : Fin k → ℕ) (s : Finset K)
    (hf : ∀ l, f l < s.card) (hg : ∀ l, g l < s.card)
    (h : ∀ t ∈ s, ∑ l : Fin k, d l * t ^ f l = ∑ l : Fin k, d l * t ^ g l) :
    expPoly k d f = expPoly k d g :=
  eq_of_degrees_lt_of_eval_finset_eq s (degree_expPoly_lt d f hf)
    (degree_expPoly_lt d g hg) fun t ht => by rw [eval_expPoly, eval_expPoly]; exact h t ht

theorem expPoly_coeff_two_pow {k : ℕ} (d : Fin k → K) (l₀ : Fin k) :
    (expPoly k d fun l => 2 ^ (l : ℕ)).coeff (2 ^ (l₀ : ℕ)) = d l₀ := by
  rw [expPoly_coeff, Finset.sum_eq_single l₀]
  · simp
  · intro l _ hl
    have hne : 2 ^ (l₀ : ℕ) ≠ 2 ^ (l : ℕ) := fun h =>
      hl (Fin.ext (Nat.pow_right_injective (le_refl 2) h).symm)
    simp [hne]
  · simp

end ExpPoly

section Linearized

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

@[expose] noncomputable def linearizedMap (k : ℕ) (d : Fin k → K) : K →+ K where
  toFun t := ∑ l : Fin k, d l * t ^ (2 ^ (l : ℕ))
  map_zero' := by simp [zero_pow (Nat.two_pow_pos _).ne']
  map_add' x y := by
    simp only [add_pow_char_pow, mul_add, Finset.sum_add_distrib]

omit [Fintype K] in
theorem linearizedMap_apply (k : ℕ) (d : Fin k → K) (t : K) :
    linearizedMap k d t = ∑ l : Fin k, d l * t ^ (2 ^ (l : ℕ)) := rfl

theorem linearizedMap_injective {k : ℕ} (hk : Fintype.card K = 2 ^ k) :
    Function.Injective (linearizedMap (K := K) k) := by
  intro d d' hdd
  have hz : ∀ t, ∑ l : Fin k, (d l - d' l) * t ^ (2 ^ (l : ℕ)) = 0 := by
    intro t
    have := DFunLike.congr_fun hdd t
    simp only [linearizedMap_apply] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this, sub_self]
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
      omega
    · exact h
  have hP : expPoly k (fun l => d l - d' l) (fun l => 2 ^ (l : ℕ)) = 0 := by
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero (Finset.univ : Finset K) ?_ ?_
    · rw [Finset.card_univ, hk]
      refine degree_expPoly_lt _ _ fun l => ?_
      exact Nat.pow_lt_pow_right (by norm_num) l.2
    · intro t _
      rw [eval_expPoly]
      exact hz t
  funext l
  have := expPoly_coeff_two_pow (fun l => d l - d' l) l
  rw [hP, coeff_zero] at this
  exact sub_eq_zero.mp this.symm

theorem exists_linearized {k : ℕ} (hk : Fintype.card K = 2 ^ k) (h : K →+ K) :
    ∃ d : Fin k → K, ∀ t, h t = ∑ l : Fin k, d l * t ^ (2 ^ (l : ℕ)) := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have hrank : Module.finrank (ZMod 2) K = k := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hk, ZMod.card] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  let B := Module.finBasis (ZMod 2) K
  have hev : Function.Injective
      fun (g : K →+ K) (i : Fin (Module.finrank (ZMod 2) K)) => g (B i) := by
    intro g g' hgg
    have : AddMonoidHom.toZModLinearMap 2 g = AddMonoidHom.toZModLinearMap 2 g' :=
      B.ext fun i => congrFun hgg i
    exact DFunLike.ext _ _ fun t => DFunLike.congr_fun this t
  have : Finite (K →+ K) := Finite.of_injective _ hev
  have hle : Nat.card (K →+ K) ≤ Nat.card (Fin k → K) := by
    calc Nat.card (K →+ K) ≤ Nat.card (Fin (Module.finrank (ZMod 2) K) → K) :=
          Nat.card_le_card_of_injective _ hev
      _ = Nat.card (Fin k → K) := by rw [hrank]
  have hbij := (linearizedMap_injective (K := K) hk).bijective_of_nat_card_le hle
  obtain ⟨d, hd⟩ := hbij.2 h
  exact ⟨d, fun t => by rw [← hd, linearizedMap_apply]⟩

end Linearized

end CFSG.CGT.PushingUpLit.SolKNA
