module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterGF64
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open scoped Matrix

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64

@[expose] def toMat3 (A : Array GF64) : Matrix (Fin 3) (Fin 3) GF64 :=
  Matrix.of fun i j => A.getD (3 * i.val + j.val) 0

@[expose] def ofMat3 (M : Matrix (Fin 3) (Fin 3) GF64) : Array GF64 :=
  Array.ofFn (n := 9) fun t => M ⟨t.val / 3, by omega⟩ ⟨t.val % 3, by omega⟩

@[expose] def mulArr3 (A B : Array GF64) : Array GF64 :=
  Array.ofFn (n := 9) fun t =>
    let i := t.val / 3
    let j := t.val % 3
    A.getD (3 * i) 0 * B.getD j 0 + A.getD (3 * i + 1) 0 * B.getD (3 + j) 0 +
      A.getD (3 * i + 2) 0 * B.getD (6 + j) 0

@[expose] def oneArr3 : Array GF64 := ofMat3 1

@[expose] def sigArr (A : Array GF64) : Array GF64 := A.map sigma2

@[expose] def smulArr3 (c : GF64) (A : Array GF64) : Array GF64 := A.map (c * ·)

@[expose] def conjTrArr3 (A : Array GF64) : Array GF64 :=
  Array.ofFn (n := 9) fun t => barC (A.getD (3 * (t.val % 3) + t.val / 3) 0)

theorem size_ofMat3 (M : Matrix (Fin 3) (Fin 3) GF64) : (ofMat3 M).size = 9 := by
  simp [ofMat3]

theorem size_mulArr3 (A B : Array GF64) : (mulArr3 A B).size = 9 := by simp [mulArr3]

theorem size_oneArr3 : oneArr3.size = 9 := size_ofMat3 1

theorem size_sigArr (A : Array GF64) : (sigArr A).size = A.size := by simp [sigArr]

theorem size_smulArr3 (c : GF64) (A : Array GF64) : (smulArr3 c A).size = A.size := by
  simp [smulArr3]

theorem size_conjTrArr3 (A : Array GF64) : (conjTrArr3 A).size = 9 := by simp [conjTrArr3]

theorem getD_ofFn9 (f : Fin 9 → GF64) (t : ℕ) (h : t < 9) :
    (Array.ofFn f).getD t 0 = f ⟨t, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem toMat3_ofMat3 (M : Matrix (Fin 3) (Fin 3) GF64) : toMat3 (ofMat3 M) = M := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat3, ofMat3, Matrix.of_apply]
  rw [getD_ofFn9 _ _ (by omega)]
  congr 1 <;> (ext; simp; try omega)

theorem toMat3_mulArr3 (A B : Array GF64) : toMat3 (mulArr3 A B) = toMat3 A * toMat3 B := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat3, mulArr3, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_three]
  rw [getD_ofFn9 _ _ (by omega)]
  have h1 : (3 * i.val + j.val) / 3 = i.val := by omega
  have h2 : (3 * i.val + j.val) % 3 = j.val := by omega
  simp only [h1, h2]
  simp

theorem eq_of_toMat_eq3 {A B : Array GF64} (hA : A.size = 9) (hB : B.size = 9)
    (h : toMat3 A = toMat3 B) : A = B := by
  apply Array.ext (hA.trans hB.symm)
  intro t ht ht'
  have h9 : t < 9 := hA ▸ ht
  have := congrFun (congrFun h ⟨t / 3, by omega⟩) ⟨t % 3, by omega⟩
  simp only [toMat3, Matrix.of_apply] at this
  have e : 3 * (t / 3) + t % 3 = t := by omega
  rw [e] at this
  simpa [Array.getD_eq_getD_getElem?, ht, ht'] using this

theorem toMat3_sigArr (A : Array GF64) :
    toMat3 (sigArr A) = (toMat3 A).map sigma2 := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat3, sigArr, Matrix.of_apply, Matrix.map_apply, Array.getD_eq_getD_getElem?,
    Array.getElem?_map]
  cases A[3 * i.val + j.val]? <;> simp [map_zero]

theorem toMat3_smulArr3 (c : GF64) (A : Array GF64) :
    toMat3 (smulArr3 c A) = c • toMat3 A := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat3, smulArr3, Matrix.of_apply, Matrix.smul_apply, Array.getD_eq_getD_getElem?,
    Array.getElem?_map, smul_eq_mul]
  cases A[3 * i.val + j.val]? <;> simp

theorem toMat3_conjTrArr3 (A : Array GF64) :
    toMat3 (conjTrArr3 A) = ((toMat3 A).map barC)ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [toMat3, conjTrArr3, Matrix.of_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [getD_ofFn9 _ _ (by omega)]
  have h1 : (3 * i.val + j.val) % 3 = j.val := by omega
  have h2 : (3 * i.val + j.val) / 3 = i.val := by omega
  simp only [h1, h2]

theorem toMat3_oneArr3 : toMat3 oneArr3 = 1 := toMat3_ofMat3 1

end CFSG.AGLEmbedding.ChevOuter.U38
