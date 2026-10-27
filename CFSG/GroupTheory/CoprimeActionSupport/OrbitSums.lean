module


public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Order.CompletePartialOrder

public section

open scoped Fin.NatCast

namespace CFSG.GroupTheory.CoprimeActionSupport.OrbitSums

theorem exists_fixed {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (r : ℕ) [NeZero r] (σ : V ≃ₗ[F] V) (hσ : σ ^ r = 1)
    (W : Fin r → Submodule F V) (hW : iSupIndep W)
    (hmap : ∀ i : Fin r, ∀ v ∈ W i, σ v ∈ W (i + 1))
    (h0 : W 0 ≠ ⊥) :
    ∃ v : V, v ≠ 0 ∧ σ v = v := by
  obtain ⟨v0, hv0, hne⟩ := (Submodule.ne_bot_iff _).1 h0
  have hmem : ∀ n : ℕ, (σ ^ n) v0 ∈ W (n : Fin r) := by
    intro n
    induction n with
    | zero => simpa using hv0
    | succ n ih =>
      have := hmap _ _ ih
      rw [pow_succ', LinearEquiv.mul_apply]
      simpa [Nat.cast_succ] using this
  set f : ℕ → V := fun n => (σ ^ n) v0 with hf
  have hfr : f r = f 0 := by simp [hf, hσ]
  refine ⟨∑ i : Fin r, f i, ?_, ?_⟩
  · intro hS
    have hsplit := Finset.add_sum_erase Finset.univ (fun i : Fin r => f i) (Finset.mem_univ 0)
    have hrest : ∑ i ∈ Finset.univ.erase (0 : Fin r), f i ∈ ⨆ j ≠ (0 : Fin r), W j := by
      refine Submodule.sum_mem _ fun i hi => ?_
      have hi' : i ≠ 0 := Finset.ne_of_mem_erase hi
      have h1 : f i ∈ W i := by
        have := hmem i
        simpa [hf] using this
      exact (le_iSup₂ (f := fun j (_ : j ≠ (0 : Fin r)) => W j) i hi') h1
    have hf0 : f ((0 : Fin r) : ℕ) = v0 := by simp [hf]
    rw [hS, hf0] at hsplit
    have hv0' : v0 ∈ W 0 := hv0
    have hneg : v0 ∈ ⨆ j ≠ (0 : Fin r), W j := by
      have : v0 = -(∑ i ∈ Finset.univ.erase (0 : Fin r), f i) := by
        rw [eq_neg_iff_add_eq_zero]; exact hsplit
      rw [this]; exact Submodule.neg_mem _ hrest
    exact hne (by simpa using (Submodule.disjoint_def.1 (hW 0)) v0 hv0' hneg)
  · rw [map_sum]
    have key : ∀ i : Fin r, σ (f i) = f (i + 1) := by
      intro i
      simp [hf, pow_succ', LinearEquiv.mul_apply]
    simp_rw [key]
    rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1)) r, Fin.sum_univ_eq_sum_range f r]
    have h1 := Finset.sum_range_succ' f r
    have h2 := Finset.sum_range_succ f r
    rw [hfr] at h2
    have : ∑ i ∈ Finset.range r, f (i + 1) = ∑ i ∈ Finset.range r, f i := by
      have := h1.symm.trans h2
      simpa using this
    exact this

end CFSG.GroupTheory.CoprimeActionSupport.OrbitSums
