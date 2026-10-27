module

public import Mathlib.Algebra.Polynomial.Roots

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Polynomial

theorem setOf_eval_eq_zero_eq_coe_toFinset_roots {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] {f : R[X]} (hf : f ≠ 0) :
    {a : R | f.eval a = 0} = (f.roots.toFinset : Set R) := by
  ext a; simp [hf]

theorem ncard_setOf_eval_eq_zero_le_natDegree {R : Type*} [CommRing R] [IsDomain R] {f : R[X]}
    (hf : f ≠ 0) : {a : R | f.eval a = 0}.ncard ≤ f.natDegree := by
  classical
  have hsub : f.roots.toFinset.val ⊆ f.roots := by
    rw [Multiset.toFinset_val]; exact Multiset.dedup_subset _
  rw [setOf_eval_eq_zero_eq_coe_toFinset_roots hf, Set.ncard_coe_finset]
  exact card_le_degree_of_subset_roots hsub

theorem ncard_le_natDegree_of_forall_eval_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} (hf : f ≠ 0) {s : Set R} (hs : ∀ a ∈ s, f.eval a = 0) : s.ncard ≤ f.natDegree :=
  le_trans (Set.ncard_le_ncard (fun _ ha => hs _ ha) (f.finite_setOfPred_isRoot hf))
    (ncard_setOf_eval_eq_zero_le_natDegree hf)

theorem card_le_natDegree_of_forall_eval_eq_zero {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} (hf : f ≠ 0) {s : Finset R} (hs : ∀ a ∈ s, f.eval a = 0) :
    s.card ≤ f.natDegree := by
  rw [← Set.ncard_coe_finset]
  exact ncard_le_natDegree_of_forall_eval_eq_zero hf (by simpa using hs)

theorem finite_setOf_eval_eq_zero {R : Type*} [CommRing R] [IsDomain R] {f : R[X]} (hf : f ≠ 0) :
    {a : R | f.eval a = 0}.Finite :=
  f.finite_setOfPred_isRoot hf

end

end CFSG.FeitThompson
