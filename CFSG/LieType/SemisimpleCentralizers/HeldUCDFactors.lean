module

public import Mathlib.FieldTheory.Separable

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L]

@[expose] noncomputable def factorsOf (m : ℕ) : Finset L[X] :=
  (UniqueFactorizationMonoid.normalizedFactors (X ^ m - 1 : L[X])).toFinset

theorem mem_factorsOf_iff {m : ℕ} {f : L[X]} :
    f ∈ factorsOf (L := L) m ↔
      f ∈ UniqueFactorizationMonoid.normalizedFactors (X ^ m - 1 : L[X]) := by
  unfold factorsOf
  exact Multiset.mem_toFinset

theorem factorsOf_irreducible {m : ℕ} {f : L[X]} (hf : f ∈ factorsOf (L := L) m) :
    Irreducible f := by
  exact UniqueFactorizationMonoid.irreducible_of_normalized_factor f (mem_factorsOf_iff.mp hf)

theorem factorsOf_monic {m : ℕ} {f : L[X]} (hf : f ∈ factorsOf (L := L) m) : Monic f := by
  have hn := UniqueFactorizationMonoid.normalize_normalized_factor f (mem_factorsOf_iff.mp hf)
  have hne : f ≠ 0 := (factorsOf_irreducible hf).ne_zero
  have h := Polynomial.monic_normalize hne
  convert h using 1
  exact hn.symm

theorem squarefree_X_pow_sub_one {m : ℕ} (hm0 : (m : L) ≠ 0) :
    Squarefree (X ^ m - 1 : L[X]) := by
  have hsep : (X ^ m - C (1 : L)).Separable :=
    Polynomial.separable_X_pow_sub_C (1 : L) hm0 one_ne_zero
  rw [map_one] at hsep
  exact hsep.squarefree

theorem X_pow_sub_one_monic {m : ℕ} (hm : 0 < m) : (X ^ m - 1 : L[X]).Monic := by
  simpa using Polynomial.monic_X_pow_sub_C (1 : L) (by omega : m ≠ 0)

theorem X_pow_sub_one_ne_zero {m : ℕ} (hm : 0 < m) : (X ^ m - 1 : L[X]) ≠ 0 :=
  (X_pow_sub_one_monic (L := L) hm).ne_zero

theorem prod_factorsOf {m : ℕ} (hm0 : (m : L) ≠ 0) (hm : 0 < m) :
    ∏ f ∈ factorsOf (L := L) m, f = X ^ m - 1 := by
  have hne : (X ^ m - 1 : L[X]) ≠ 0 := X_pow_sub_one_ne_zero (L := L) hm
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hne).mp
    (squarefree_X_pow_sub_one hm0)
  have hassoc := UniqueFactorizationMonoid.prod_normalizedFactors hne
  have hmon : ∀ g ∈ UniqueFactorizationMonoid.normalizedFactors (X ^ m - 1 : L[X]), Monic g := by
    intro g hg
    have hn := UniqueFactorizationMonoid.normalize_normalized_factor g hg
    have hg0 : g ≠ 0 := (UniqueFactorizationMonoid.irreducible_of_normalized_factor g hg).ne_zero
    have h := Polynomial.monic_normalize hg0
    convert h using 1
    exact hn.symm
  have hprodmon : (UniqueFactorizationMonoid.normalizedFactors (X ^ m - 1 : L[X])).prod.Monic := by
    have := Polynomial.monic_multiset_prod_of_monic
      (UniqueFactorizationMonoid.normalizedFactors (X ^ m - 1 : L[X]))
      (fun g => g) (fun g hg => hmon g hg)
    simpa using this
  have heq := Polynomial.eq_of_monic_of_associated hprodmon (X_pow_sub_one_monic hm) hassoc
  unfold factorsOf
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup,
    Multiset.map_id']
  exact heq

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
