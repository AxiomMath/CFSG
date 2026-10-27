module

public import CFSG.Quasithin.Recognition.CertTrialityModel

public section

open CFSG.Quasithin

namespace CFSG.AGLEmbedding.D4Two

@[expose] def toMat (A : Array GF8) : Matrix (Fin 8) (Fin 8) GF8 :=
  Matrix.of fun i j => A.getD (8 * i.val + j.val) 0

@[expose] def ofMat (M : Matrix (Fin 8) (Fin 8) GF8) : Array GF8 :=
  Array.ofFn (n := 64) fun t => M ⟨t.val / 8, by omega⟩ ⟨t.val % 8, by omega⟩

@[expose] def mulArr (A B : Array GF8) : Array GF8 :=
  Array.ofFn (n := 64) fun t =>
    let i := t.val / 8
    let j := t.val % 8
    A.getD (8 * i) 0 * B.getD j 0 + A.getD (8 * i + 1) 0 * B.getD (8 + j) 0 +
    A.getD (8 * i + 2) 0 * B.getD (16 + j) 0 + A.getD (8 * i + 3) 0 * B.getD (24 + j) 0 +
    A.getD (8 * i + 4) 0 * B.getD (32 + j) 0 + A.getD (8 * i + 5) 0 * B.getD (40 + j) 0 +
    A.getD (8 * i + 6) 0 * B.getD (48 + j) 0 + A.getD (8 * i + 7) 0 * B.getD (56 + j) 0

@[expose] def oneArr : Array GF8 := ofMat 1

theorem size_ofMat (M : Matrix (Fin 8) (Fin 8) GF8) : (ofMat M).size = 64 := by
  simp [ofMat]

theorem size_mulArr (A B : Array GF8) : (mulArr A B).size = 64 := by
  simp [mulArr]

theorem size_oneArr : oneArr.size = 64 := size_ofMat 1

theorem getD_ofFn (f : Fin 64 → GF8) (t : ℕ) (h : t < 64) :
    (Array.ofFn f).getD t 0 = f ⟨t, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

theorem toMat_ofMat (M : Matrix (Fin 8) (Fin 8) GF8) : toMat (ofMat M) = M := by
  ext i j
  simp only [toMat, ofMat, Matrix.of_apply]
  rw [getD_ofFn _ _ (by omega)]
  congr 1 <;> (ext; simp; try omega)

theorem toMat_mulArr (A B : Array GF8) : toMat (mulArr A B) = toMat A * toMat B := by
  ext i j
  simp only [toMat, mulArr, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_eight]
  rw [getD_ofFn _ _ (by omega)]
  have h1 : (8 * i.val + j.val) / 8 = i.val := by omega
  have h2 : (8 * i.val + j.val) % 8 = j.val := by omega
  simp only [h1, h2]
  simp

theorem eq_of_toMat_eq {A B : Array GF8} (hA : A.size = 64) (hB : B.size = 64)
    (h : toMat A = toMat B) : A = B := by
  apply Array.ext (hA.trans hB.symm)
  intro t ht ht'
  have h64 : t < 64 := hA ▸ ht
  have := congrFun (congrFun h ⟨t / 8, by omega⟩) ⟨t % 8, by omega⟩
  simp only [toMat, Matrix.of_apply] at this
  have e : 8 * (t / 8) + t % 8 = t := by omega
  rw [e] at this
  simpa [Array.getD_eq_getD_getElem?, ht, ht'] using this

theorem trialityElt_mul_self : ∀ (a : GF8) (s : Bool), trialityElt a s * trialityElt a s = 1 := by
  decide +kernel

theorem trialityMid_mul_self : ∀ s : Bool, trialityMid s * trialityMid s = 1 := by
  decide +kernel

@[expose] def letterMat (i : ℕ) : Matrix (Fin 8) (Fin 8) GF8 :=
  if i < 8 then trialityElt (GF8.ofNat' i) true
  else if i < 16 then trialityElt (GF8.ofNat' (i - 8)) false
  else if i = 16 then trialityMid true else trialityMid false

theorem letterMat_mul_self (i : ℕ) : letterMat i * letterMat i = 1 := by
  unfold letterMat
  split_ifs
  · exact trialityElt_mul_self _ _
  · exact trialityElt_mul_self _ _
  · exact trialityMid_mul_self _
  · exact trialityMid_mul_self _

theorem letterMat_mem (i : ℕ) : letterMat i ∈ trialityGens8 := by
  unfold letterMat
  split_ifs
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inr ⟨_, rfl⟩

@[expose] def letterGL (i : ℕ) : GL (Fin 8) GF8 :=
  ⟨letterMat i, letterMat i, letterMat_mul_self i, letterMat_mul_self i⟩

theorem letterGL_mem (i : ℕ) : letterGL i ∈ trialityGroup8 :=
  Subgroup.subset_closure (letterMat_mem i)

@[expose] def wordGL (w : List ℕ) : GL (Fin 8) GF8 := (w.map letterGL).prod

theorem wordGL_mem (w : List ℕ) : wordGL w ∈ trialityGroup8 := by
  unfold wordGL
  exact Subgroup.list_prod_mem _ (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact letterGL_mem i)

@[expose] def letterArr (i : ℕ) : Array GF8 := ofMat (letterMat i)

@[expose] def wordArr (w : List ℕ) : Array GF8 :=
  w.foldr (fun l A => mulArr (letterArr l) A) oneArr

theorem wordArr_nil : wordArr [] = oneArr := rfl

theorem wordArr_cons (l : ℕ) (w : List ℕ) :
    wordArr (l :: w) = mulArr (letterArr l) (wordArr w) := rfl

theorem size_wordArr (w : List ℕ) : (wordArr w).size = 64 := by
  induction w with
  | nil => rw [wordArr_nil]; exact size_oneArr
  | cons l w ih => rw [wordArr_cons]; exact size_mulArr _ _

theorem coe_wordGL (w : List ℕ) :
    ((wordGL w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat (wordArr w) := by
  induction w with
  | nil => rw [wordArr_nil, oneArr, toMat_ofMat]; rfl
  | cons l w ih =>
    show (letterMat l) * ((wordGL w : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
    rw [ih, wordArr_cons, toMat_mulArr, letterArr, toMat_ofMat]

end CFSG.AGLEmbedding.D4Two
