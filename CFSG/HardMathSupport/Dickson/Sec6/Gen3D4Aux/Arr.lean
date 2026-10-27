module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterGF64
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.AGLEmbedding.ChevOuter

@[expose] def toMat (A : Array GF64) : Matrix (Fin 8) (Fin 8) GF64 :=
  Matrix.of fun i j => A.getD (8 * i.val + j.val) 0

@[expose] def ofMat (M : Matrix (Fin 8) (Fin 8) GF64) : Array GF64 :=
  Array.ofFn (n := 64) fun t => M ⟨t.val / 8, by omega⟩ ⟨t.val % 8, by omega⟩

@[expose] def mulArr (A B : Array GF64) : Array GF64 :=
  Array.ofFn (n := 64) fun t =>
    let i := t.val / 8
    let j := t.val % 8
    A.getD (8 * i) 0 * B.getD j 0 + A.getD (8 * i + 1) 0 * B.getD (8 + j) 0 +
    A.getD (8 * i + 2) 0 * B.getD (16 + j) 0 + A.getD (8 * i + 3) 0 * B.getD (24 + j) 0 +
    A.getD (8 * i + 4) 0 * B.getD (32 + j) 0 + A.getD (8 * i + 5) 0 * B.getD (40 + j) 0 +
    A.getD (8 * i + 6) 0 * B.getD (48 + j) 0 + A.getD (8 * i + 7) 0 * B.getD (56 + j) 0

@[expose] def oneArr : Array GF64 := ofMat 1

theorem size_ofMat (M : Matrix (Fin 8) (Fin 8) GF64) : (ofMat M).size = 64 := by
  simp [ofMat]

theorem size_mulArr (A B : Array GF64) : (mulArr A B).size = 64 := by
  simp [mulArr]

theorem size_oneArr : oneArr.size = 64 := size_ofMat 1

theorem getD_ofFn (f : Fin 64 → GF64) (t : ℕ) (h : t < 64) :
    (Array.ofFn f).getD t 0 = f ⟨t, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem toMat_ofMat (M : Matrix (Fin 8) (Fin 8) GF64) : toMat (ofMat M) = M := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat, ofMat, Matrix.of_apply]
  rw [getD_ofFn _ _ (by omega)]
  congr 1 <;> (ext; simp; try omega)

theorem toMat_mulArr (A B : Array GF64) : toMat (mulArr A B) = toMat A * toMat B := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat, mulArr, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]
  rw [getD_ofFn _ _ (by omega)]
  have h1 : (8 * i.val + j.val) / 8 = i.val := by omega
  have h2 : (8 * i.val + j.val) % 8 = j.val := by omega
  simp only [h1, h2]
  simp

theorem eq_of_toMat_eq {A B : Array GF64} (hA : A.size = 64) (hB : B.size = 64)
    (h : toMat A = toMat B) : A = B := by
  apply Array.ext (hA.trans hB.symm)
  intro t ht ht'
  have h64 : t < 64 := hA ▸ ht
  have := congrFun (congrFun h ⟨t / 8, by omega⟩) ⟨t % 8, by omega⟩
  simp only [toMat, Matrix.of_apply] at this
  have e : 8 * (t / 8) + t % 8 = t := by omega
  rw [e] at this
  simpa [Array.getD_eq_getD_getElem?, ht, ht'] using this

@[expose] def frobF : GF64 →+* GF64 := GF64.sigma2

theorem frobF_apply (a : GF64) : frobF a = a ^ 4 := GF64.sigma2_eq_pow a

theorem frobF_cube (a : GF64) : frobF (frobF (frobF a)) = a := GF64.sigma2_cube a

@[expose] def frobArr (A : Array GF64) : Array GF64 := A.map frobF

@[expose] def frobPow : ℕ → Array GF64 → Array GF64
  | 0, A => A
  | n + 1, A => frobArr (frobPow n A)

theorem getD_frobArr (A : Array GF64) (t : ℕ) :
    (frobArr A).getD t 0 = frobF (A.getD t 0) := by
  simp only [frobArr, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> simp

theorem size_frobArr (A : Array GF64) : (frobArr A).size = A.size := by simp [frobArr]

theorem toMat_frobArr (A : Array GF64) : toMat (frobArr A) = (toMat A).map frobF := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat, Matrix.of_apply, Matrix.map_apply]
  exact getD_frobArr A _

theorem toMat_frobPow (n : ℕ) (A : Array GF64) :
    toMat (frobPow n A) =
      ((fun M : Matrix (Fin 8) (Fin 8) GF64 => M.map frobF)^[n]) (toMat A) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, toMat_frobArr, ih, Function.iterate_succ_apply']

theorem size_frobPow (n : ℕ) (A : Array GF64) : (frobPow n A).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, size_frobArr, ih]

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
