module
import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset

theorem prod_le_arith_mean_pow_card {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∏ i ∈ s, f i ≤ ((∑ i ∈ s, f i) / #s) ^ #s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hcard : (#s : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hs.card_ne_zero
  have hprod : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf
  have key : (∏ i ∈ s, f i) ^ ((#s : ℝ)⁻¹) ≤ (∑ i ∈ s, f i) / #s := by
    have h := Real.geom_mean_le_arith_mean_weighted s (fun _ => (#s : ℝ)⁻¹) f
      (fun i _ => by positivity)
      (by simp only [Finset.sum_const, nsmul_eq_mul]; field_simp) hf
    rw [Real.finsetProd_rpow s f hf] at h
    calc (∏ i ∈ s, f i) ^ ((#s : ℝ)⁻¹) ≤ ∑ i ∈ s, (#s : ℝ)⁻¹ * f i := h
      _ = (∑ i ∈ s, f i) / #s := by rw [← Finset.mul_sum]; ring
  calc ∏ i ∈ s, f i = ((∏ i ∈ s, f i) ^ ((#s : ℝ)⁻¹)) ^ #s :=
        (Real.rpow_inv_natCast_pow hprod hs.card_ne_zero).symm
    _ ≤ ((∑ i ∈ s, f i) / #s) ^ #s :=
        pow_le_pow_left₀ (Real.rpow_nonneg hprod _) key _

theorem card_le_sum_of_one_le_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ} (hs : s.Nonempty)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : 1 ≤ ∏ i ∈ s, f i) : (#s : ℝ) ≤ ∑ i ∈ s, f i := by
  have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hf
  have hm : 0 ≤ (∑ i ∈ s, f i) / #s := by positivity
  have h1 : (1 : ℝ) ≤ ((∑ i ∈ s, f i) / #s) ^ #s :=
    h.trans (prod_le_arith_mean_pow_card s f hf)
  have h2 := (one_le_pow_iff_of_nonneg hm hs.card_ne_zero).1 h1
  have hcard : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  rw [le_div_iff₀ hcard] at h2
  linarith

theorem prod_le_arith_mean_pow (d : ℕ) (t : Fin d → ℝ) (ht : ∀ j, 0 < t j) :
    ∏ j, t j ≤ ((∑ j, t j) / d) ^ d := by
  simpa using prod_le_arith_mean_pow_card (Finset.univ : Finset (Fin d)) t
    (fun j _ => (ht j).le)

theorem le_sum_of_one_le_prod {d : ℕ} (hd : 0 < d) (t : Fin d → ℝ) (ht : ∀ j, 0 < t j)
    (h : 1 ≤ ∏ j, t j) : (d : ℝ) ≤ ∑ j, t j := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  simpa using card_le_sum_of_one_le_prod (s := (Finset.univ : Finset (Fin d))) (f := t)
    hne (fun j _ => (ht j).le) h

theorem arith_mean_pos {d : ℕ} (hd : 0 < d) (t : Fin d → ℝ) (ht : ∀ j, 0 < t j) :
    0 < (∑ j, t j) / d := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have hsum : 0 < ∑ j, t j := Finset.sum_pos (fun j _ => ht j) hne
  have : (0 : ℝ) < d := by exact_mod_cast hd
  positivity

end CFSG.FeitThompson
