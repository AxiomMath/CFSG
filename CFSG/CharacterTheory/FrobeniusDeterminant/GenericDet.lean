module

public import CFSG.CharacterTheory.FrobeniusDeterminant.Defs
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

open MvPolynomial Matrix

namespace FrobeniusDeterminant

lemma genericDet_isHomogeneous (n : Type*) [Fintype n] [DecidableEq n]
    (R : Type*) [CommRing R] :
    (Matrix.det (Matrix.mvPolynomialX n n R)).IsHomogeneous (Fintype.card n) := by
  have aux : Fintype.card n = 0 + ∑ i : n, 1 := by
    simp only [zero_add, Finset.sum_const, smul_eq_mul, mul_one, Fintype.card]
  simp only [aux, Matrix.det_apply', Matrix.mvPolynomialX_apply,
    ]
  apply IsHomogeneous.sum
  rintro σ -
  apply IsHomogeneous.mul
  · apply isHomogeneous_C
  apply IsHomogeneous.prod
  intro i hi
  exact isHomogeneous_X _ _

lemma irreducible_rename_of_injective {σ τ : Type*} (f : σ → τ)
    (hf : Function.Injective f) {p : MvPolynomial σ ℂ}
    (hp : Irreducible p) : Irreducible (MvPolynomial.rename f p) := by
  let e : σ ≃ Set.range f := Equiv.ofInjective f hf
  have he : Irreducible (MvPolynomial.rename e p) :=
    (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℂ e)).2 hp
  have hprime : Prime
      (MvPolynomial.rename Subtype.val (MvPolynomial.rename e p)) :=
    (MvPolynomial.prime_rename_iff (Set.range f)).2 he.prime
  apply Prime.irreducible
  convert hprime using 1
  rw [← AlgHom.comp_apply, MvPolynomial.rename_comp_rename]
  congr 2

private noncomputable def genericMinor (n : ℕ) (j : Fin (n + 2)) :
    MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ :=
  ((Matrix.mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℂ).submatrix
    Fin.succ j.succAbove).det

private lemma genericMinor_eq_rename (n : ℕ) (j : Fin (n + 2)) :
    genericMinor n j =
      MvPolynomial.rename
        (fun ab : Fin (n + 1) × Fin (n + 1) =>
          (ab.1.succ, j.succAbove ab.2))
        (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) ℂ).det := by
  rw [genericMinor, AlgHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX_apply]

private noncomputable def genericRemainder (n : ℕ) :
    MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ :=
  ∑ j : Fin (n + 1),
    (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ (j.succ : ℕ) *
      MvPolynomial.X (0, j.succ) * genericMinor n j.succ

private lemma genericDet_decompose (n : ℕ) :
    (Matrix.mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℂ).det =
      genericMinor n 0 * MvPolynomial.X (0, 0) + genericRemainder n := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Matrix.mvPolynomialX_apply, genericRemainder, genericMinor]
  simp [mul_comm]

private lemma zero_not_mem_genericMinor_vars (n : ℕ) (j : Fin (n + 2)) :
    (0, 0) ∉ (genericMinor n j).vars := by
  rw [genericMinor_eq_rename]
  intro h
  obtain ⟨ab, hab, heq⟩ := MvPolynomial.mem_vars_rename _ _ h
  exact Fin.succ_ne_zero ab.1 (congrArg Prod.fst heq)

private lemma zero_not_mem_genericRemainder_vars (n : ℕ) :
    (0, 0) ∉ (genericRemainder n).vars := by
  intro h
  have hs := MvPolynomial.vars_sum_subset (Finset.univ : Finset (Fin (n + 1)))
    (fun j =>
      (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ (j.succ : ℕ) *
        MvPolynomial.X (0, j.succ) * genericMinor n j.succ) h
  obtain ⟨j, hj, hterm⟩ := Finset.mem_biUnion.mp hs
  have hmul := MvPolynomial.vars_mul
    ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ (j.succ : ℕ) *
      MvPolynomial.X (0, j.succ)) (genericMinor n j.succ) hterm
  rcases Finset.mem_union.mp hmul with hleft | hright
  · have hmul' := MvPolynomial.vars_mul
      ((-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ (j.succ : ℕ))
      (MvPolynomial.X (0, j.succ)) hleft
    rcases Finset.mem_union.mp hmul' with hconst | hx
    · have hcpow :
          (-1 : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ) ^ (j.succ : ℕ) =
            MvPolynomial.C ((-1 : ℂ) ^ (j.succ : ℕ)) := by
          rw [map_pow, map_neg, map_one]
      rw [hcpow, MvPolynomial.vars_C] at hconst
      simpa using hconst
    · have hx' : (0 : Fin (n + 2)) = j.succ := by
        simpa using hx
      exact Fin.succ_ne_zero j hx'.symm
  · exact zero_not_mem_genericMinor_vars n j.succ hright

private lemma genericMinor_zero_irreducible (n : ℕ)
    (h : Irreducible
      (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) ℂ).det) :
    Irreducible (genericMinor n 0) := by
  rw [genericMinor_eq_rename]
  apply irreducible_rename_of_injective _ _ h
  intro a b hab
  apply Prod.ext
  · exact Fin.succ_injective _ (congrArg Prod.fst hab)
  · simpa using Fin.succ_injective _ (congrArg Prod.snd hab)

private noncomputable def swapEval (n : ℕ) :
    Fin (n + 2) × Fin (n + 2) → ℂ :=
  fun ab => Equiv.Perm.permMatrix ℂ
    (Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2))) ab.1 ab.2

private lemma eval_genericDet_swap (n : ℕ) :
  MvPolynomial.eval (swapEval n)
      (Matrix.mvPolynomialX (Fin (n + 2)) (Fin (n + 2)) ℂ).det = -1 := by
  rw [Matrix.eval_det_mvPolynomialX]
  change (Equiv.Perm.permMatrix ℂ
    (Equiv.swap (0 : Fin (n + 2)) (1 : Fin (n + 2)))).det = -1
  rw [Matrix.det_permutation]
  rw [Equiv.Perm.sign_swap]
  · norm_num
  · norm_num

private lemma eval_genericMinor_zero_swap (n : ℕ) :
    MvPolynomial.eval (swapEval n) (genericMinor n 0) = 0 := by
  rw [genericMinor_eq_rename, MvPolynomial.eval_rename]
  rw [Matrix.eval_det_mvPolynomialX]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro b
  simp [swapEval, Equiv.Perm.permMatrix]
  exact Ne.symm (Fin.succ_ne_zero b)

private lemma eval_genericRemainder_swap_ne_zero (n : ℕ) :
    MvPolynomial.eval (swapEval n) (genericRemainder n) ≠ 0 := by
  have h := congrArg (MvPolynomial.eval (swapEval n))
    (genericDet_decompose n)
  rw [eval_genericDet_swap, map_add, map_mul,
    eval_genericMinor_zero_swap] at h
  simp at h
  rw [← h]
  norm_num

private lemma genericMinor_zero_not_dvd_remainder (n : ℕ) :
    ¬genericMinor n 0 ∣ genericRemainder n := by
  intro hdiv
  obtain ⟨q, hq⟩ := hdiv
  have h := congrArg (MvPolynomial.eval (swapEval n)) hq
  rw [map_mul, eval_genericMinor_zero_swap] at h
  simp at h
  exact eval_genericRemainder_swap_ne_zero n h

theorem genericDet_irreducible : ∀ (n : ℕ), 0 < n →
    Irreducible
      (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det
  | 0, h => by omega
  | 1, _ => by
      rw [Matrix.det_fin_one]
      exact MvPolynomial.X_prime.irreducible
  | n + 2, _ => by
      have ih := genericDet_irreducible (n + 1) (by omega)
      have hf := genericMinor_zero_irreducible n ih
      rw [genericDet_decompose]
      apply MvPolynomial.irreducible_mul_X_add
      · exact hf.ne_zero
      · exact zero_not_mem_genericMinor_vars n 0
      · exact zero_not_mem_genericRemainder_vars n
      · exact (hf.isRelPrime_iff_not_dvd).2
          (genericMinor_zero_not_dvd_remainder n)

end FrobeniusDeterminant

end CFSG
