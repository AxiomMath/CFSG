module

public import Mathlib.FieldTheory.Finite.GaloisField

public section

open Polynomial

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [CharP L p]

def frobFixField (n : ℕ) : Subfield L := (iterateFrobenius L p n).eqLocusField (RingHom.id L)

theorem mem_frobFixField {n : ℕ} {x : L} : x ∈ frobFixField p L n ↔ x ^ p ^ n = x := by
  rw [frobFixField, RingHom.mem_eqLocusField, RingHom.id_apply, iterateFrobenius_def]

theorem rootSet_frobFixField {n : ℕ} (hn : 1 ≤ n) :
    ((frobFixField p L n : Subfield L) : Set L) = (X ^ p ^ n - X : L[X]).rootSet L := by
  ext x
  simp [mem_frobFixField, Polynomial.mem_rootSet, sub_eq_zero,
    FiniteField.X_pow_card_pow_sub_X_ne_zero L (by omega : n ≠ 0) hp.out.one_lt]

section Alg

variable [IsAlgClosed L]

theorem card_frobFixField {n : ℕ} (hn : 1 ≤ n) : Nat.card (frobFixField p L n) = p ^ n := by
  classical
  have hsep : (X ^ p ^ n - X : L[X]).Separable :=
    galois_poly_separable p (p ^ n) (dvd_pow_self p (by omega))
  have hsplit : (X ^ p ^ n - X : L[X]).Splits := IsAlgClosed.splits _
  have hdeg : (X ^ p ^ n - X : L[X]).natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq L (by omega : n ≠ 0) hp.out.one_lt
  have hsplit' : (Polynomial.map (algebraMap L L) (X ^ p ^ n - X : L[X])).Splits := by
    simpa using hsplit
  have key := card_rootSet_eq_natDegree (K := L) hsep hsplit'
  rw [hdeg] at key
  have e : ↥(frobFixField p L n) = ↥((X ^ p ^ n - X : L[X]).rootSet L) :=
    congrArg (fun S : Set L => ↥S) (rootSet_frobFixField p L hn)
  rw [Nat.card_congr (Equiv.cast e), Nat.card_eq_fintype_card, key]

theorem finite_frobFixField {n : ℕ} (hn : 1 ≤ n) : Finite (frobFixField p L n) :=
  Nat.finite_of_card_ne_zero (by rw [card_frobFixField p L hn]; exact (pow_pos hp.out.pos n).ne')

end Alg

theorem range_le_frobFixField {K : Type} [Field K] [Finite K] [Algebra K L] {m n : ℕ}
    (hK : Nat.card K = p ^ m) (hmn : m ∣ n) (x : K) :
    algebraMap K L x ∈ frobFixField p L n := by
  rw [mem_frobFixField]
  obtain ⟨k, rfl⟩ := hmn
  have h1 : x ^ p ^ m = x := by
    have := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have h2 : ∀ j : ℕ, x ^ p ^ (m * j) = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, h1]
  rw [← map_pow, h2 k]

theorem isAlgClosure_frobFixField [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    [IsAlgClosure K L] {m n : ℕ} (hK : Nat.card K = p ^ m) (hmn : m ∣ n) :
    IsAlgClosure (frobFixField p L n) L := by
  let f : K →+* frobFixField p L n :=
    (algebraMap K L).codRestrict (frobFixField p L n) (range_le_frobFixField p L hK hmn)
  let _ : Algebra K (frobFixField p L n) := f.toAlgebra
  have : IsScalarTower K (frobFixField p L n) L := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hK' : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  exact ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) (frobFixField p L n)⟩

theorem exists_subfield_isAlgClosure [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    [IsAlgClosure K L] {m n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = p ^ m) (hmn : m ∣ n) :
    ∃ (K₄ : Type) (_ : Field K₄) (_ : Finite K₄) (_ : Algebra K₄ L) (_ : IsAlgClosure K₄ L)
      (_ : CharP K₄ p), Nat.card K₄ = p ^ n ∧
        ∀ x : L, x ^ p ^ n = x → x ∈ Set.range (algebraMap K₄ L) :=
  ⟨↥(frobFixField p L n), inferInstance, finite_frobFixField p L hn, inferInstance,
    isAlgClosure_frobFixField p L hK hmn,
    (RingHom.charP_iff_charP (algebraMap (frobFixField p L n) L) p).2 inferInstance,
    card_frobFixField p L hn, fun x hx => ⟨⟨x, (mem_frobFixField p L).2 hx⟩, rfl⟩⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
