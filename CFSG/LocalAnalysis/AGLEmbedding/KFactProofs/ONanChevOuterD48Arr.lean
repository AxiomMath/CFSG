module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48GF512
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

open CFSG.Quasithin

@[expose] def toMat (A : Array GF512) : Matrix (Fin 8) (Fin 8) GF512 :=
  Matrix.of fun i j => A.getD (8 * i.val + j.val) 0

@[expose] def ofMat (M : Matrix (Fin 8) (Fin 8) GF512) : Array GF512 :=
  Array.ofFn (n := 64) fun t => M ⟨t.val / 8, by omega⟩ ⟨t.val % 8, by omega⟩

@[expose] def mulArr (A B : Array GF512) : Array GF512 :=
  Array.ofFn (n := 64) fun t =>
    let i := t.val / 8
    let j := t.val % 8
    A.getD (8 * i) 0 * B.getD j 0 + A.getD (8 * i + 1) 0 * B.getD (8 + j) 0 +
    A.getD (8 * i + 2) 0 * B.getD (16 + j) 0 + A.getD (8 * i + 3) 0 * B.getD (24 + j) 0 +
    A.getD (8 * i + 4) 0 * B.getD (32 + j) 0 + A.getD (8 * i + 5) 0 * B.getD (40 + j) 0 +
    A.getD (8 * i + 6) 0 * B.getD (48 + j) 0 + A.getD (8 * i + 7) 0 * B.getD (56 + j) 0

@[expose] def oneArr : Array GF512 := ofMat 1

theorem size_ofMat (M : Matrix (Fin 8) (Fin 8) GF512) : (ofMat M).size = 64 := by
  simp [ofMat]

theorem size_mulArr (A B : Array GF512) : (mulArr A B).size = 64 := by
  simp [mulArr]

theorem size_oneArr : oneArr.size = 64 := size_ofMat 1

theorem getD_ofFn (f : Fin 64 → GF512) (t : ℕ) (h : t < 64) :
    (Array.ofFn f).getD t 0 = f ⟨t, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem toMat_ofMat (M : Matrix (Fin 8) (Fin 8) GF512) : toMat (ofMat M) = M := by
  ext i j
  simp only [toMat, ofMat, Matrix.of_apply]
  rw [getD_ofFn _ _ (by omega)]
  congr 1 <;> (ext; simp; try omega)

theorem toMat_mulArr (A B : Array GF512) : toMat (mulArr A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, mulArr, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]
  rw [getD_ofFn _ _ (by omega)]
  have h1 : (8 * i.val + j.val) / 8 = i.val := by omega
  have h2 : (8 * i.val + j.val) % 8 = j.val := by omega
  simp only [h1, h2]
  simp

theorem eq_of_toMat_eq {A B : Array GF512} (hA : A.size = 64) (hB : B.size = 64)
    (h : toMat A = toMat B) : A = B := by
  apply Array.ext (hA.trans hB.symm)
  intro t ht ht'
  have h64 : t < 64 := hA ▸ ht
  have := congrFun (congrFun h ⟨t / 8, by omega⟩) ⟨t % 8, by omega⟩
  simp only [toMat, Matrix.of_apply] at this
  have e : 8 * (t / 8) + t % 8 = t := by omega
  rw [e] at this
  simpa [Array.getD_eq_getD_getElem?, ht, ht'] using this

theorem GF512.two_eq_zero : (2 : GF512) = 0 := by decide

instance instCharP : CharP GF512 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero GF512.two_eq_zero

theorem GF512.card_eq : Nat.card GF512 = 512 := by
  rw [Nat.card_congr (show GF512 ≃ GF8 × GF8 × GF8 from
    ⟨fun a => (a.c0, a.c1, a.c2), fun p => ⟨p.1, p.2.1, p.2.2⟩, fun _ => rfl, fun _ => rfl⟩),
    Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := GF8)]
  rfl

@[expose] def frobF : GF512 →+* GF512 := iterateFrobenius GF512 2 3

theorem frobF_apply (a : GF512) : frobF a = a ^ 8 := by
  simp [frobF, iterateFrobenius_def]

theorem frobF_cube (a : GF512) : frobF (frobF (frobF a)) = a := by
  have : Fintype GF512 := inferInstance
  have h := FiniteField.pow_card a
  have hc : Fintype.card GF512 = 512 := by
    rw [← Nat.card_eq_fintype_card]; exact GF512.card_eq
  rw [hc] at h
  rw [frobF_apply, frobF_apply, frobF_apply, ← pow_mul, ← pow_mul]
  exact h

@[expose] def frobArr (A : Array GF512) : Array GF512 := A.map frobF

@[expose] def frobPow : ℕ → Array GF512 → Array GF512
  | 0, A => A
  | n + 1, A => frobArr (frobPow n A)

theorem getD_frobArr (A : Array GF512) (t : ℕ) :
    (frobArr A).getD t 0 = frobF (A.getD t 0) := by
  simp only [frobArr, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> simp

theorem size_frobArr (A : Array GF512) : (frobArr A).size = A.size := by simp [frobArr]

theorem toMat_frobArr (A : Array GF512) : toMat (frobArr A) = (toMat A).map frobF := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.map_apply]
  exact getD_frobArr A _

theorem toMat_frobPow (n : ℕ) (A : Array GF512) :
    toMat (frobPow n A) =
      ((fun M : Matrix (Fin 8) (Fin 8) GF512 => M.map frobF)^[n]) (toMat A) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, toMat_frobArr, ih, Function.iterate_succ_apply']

theorem size_frobPow (n : ℕ) (A : Array GF512) : (frobPow n A).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, size_frobArr, ih]

end CFSG.AGLEmbedding.ChevOuterD48
