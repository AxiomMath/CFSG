module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Polynomial

variable {K : Type*} [CommRing K]

noncomputable def bgCubic (c : K) : K[X] := X * (X - 2) * (X - C c) + (X - 1)

@[simp]
theorem bgCubic_eval (c x : K) :
    (bgCubic c).eval x = x * (x - 2) * (x - c) + (x - 1) := by
  simp [bgCubic]

theorem bgCubic_monic [Nontrivial K] (c : K) : (bgCubic c).Monic := by
  unfold bgCubic
  monicity!

theorem natDegree_bgCubic [Nontrivial K] (c : K) : (bgCubic c).natDegree = 3 := by
  unfold bgCubic
  compute_degree!

theorem bgCubic_ne_zero [Nontrivial K] (c : K) : bgCubic c ≠ 0 := (bgCubic_monic c).ne_zero

@[simp]
theorem bgCubic_eval_zero (c : K) : (bgCubic c).eval 0 = -1 := by simp

@[simp]
theorem bgCubic_eval_two (c : K) : (bgCubic c).eval 2 = 1 := by simp; norm_num

theorem exists_bgCubic_no_root (K : Type*) [Field K] [Finite K] :
    ∃ c : K, ∀ x : K, ¬ (bgCubic c).IsRoot x := by
  by_contra h
  simp only [not_exists, not_forall, not_not] at h
  choose g hg using h
  simp only [IsRoot.def, bgCubic_eval] at hg
  have hg0 : ∀ c : K, g c ≠ 0 := by
    intro c hc
    have h' := hg c
    rw [hc] at h'
    simp only [zero_mul, zero_sub, zero_add] at h'
    exact one_ne_zero (neg_eq_zero.mp h')
  have hgtwo : ∀ c : K, g c ≠ 2 := by
    intro c hc
    have h' := hg c
    rw [hc] at h'
    norm_num at h'
  have hinj : Function.Injective g := by
    intro c e hce
    have h1 := hg c
    have h2 := hg e
    rw [hce] at h1
    have key : g e * (g e - 2) * (e - c) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp key with hk | hk
    · rcases mul_eq_zero.mp hk with hk | hk
      · exact absurd hk (hg0 e)
      · exact absurd (sub_eq_zero.mp hk) (hgtwo e)
    · exact (sub_eq_zero.mp hk).symm
  obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.mp hinj 0
  exact hg0 c hc

theorem exists_bgCubic_zmod_no_root (p : ℕ) [Fact p.Prime] :
    ∃ c : ZMod p, ∀ x : ZMod p, ¬ (bgCubic c).IsRoot x :=
  exists_bgCubic_no_root (ZMod p)

theorem exists_bgCubic_roots_eq_zero (K : Type*) [Field K] [Finite K] :
    ∃ c : K, (bgCubic c).roots = 0 := by
  obtain ⟨c, hc⟩ := exists_bgCubic_no_root K
  exact ⟨c, Multiset.eq_zero_of_forall_notMem fun x hx => hc x (mem_roots'.mp hx).2⟩

end CFSG.FeitThompson
