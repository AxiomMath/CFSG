module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Arr
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

open CFSG.AGLEmbedding.ChevOuter CFSG.Quasithin
open CFSG.Open (quasithinRootElt quasithinD4Root)

@[expose] def nilM (pos : List (Fin 8 × Fin 8)) : Matrix (Fin 8) (Fin 8) GF64 :=
  Matrix.of fun r c => if (r, c) ∈ pos then 1 else 0

theorem root_eq (pos : List (Fin 8 × Fin 8)) (t : GF64) :
    quasithinRootElt pos t = 1 + t • nilM pos := by
  refine Matrix.ext fun r c => ?_
  by_cases h : (r, c) ∈ pos <;> by_cases hrc : r = c <;>
    simp [quasithinRootElt, nilM, h, hrc]

theorem root_add {pos : List (Fin 8 × Fin 8)} (h : nilM pos * nilM pos = 0) (s t : GF64) :
    quasithinRootElt pos s * quasithinRootElt pos t = quasithinRootElt pos (s + t) := by
  rw [root_eq, root_eq, root_eq]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    add_smul, h, smul_zero]
  abel

theorem root_comm {p q : List (Fin 8 × Fin 8)} (h : nilM p * nilM q = nilM q * nilM p)
    (s t : GF64) :
    quasithinRootElt p s * quasithinRootElt q t = quasithinRootElt q t * quasithinRootElt p s := by
  rw [root_eq, root_eq]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_smul, h, mul_comm s t]
  abel

theorem root_zero (pos : List (Fin 8 × Fin 8)) : quasithinRootElt pos (0 : GF64) = 1 := by
  rw [root_eq, zero_smul, add_zero]

theorem nil_sq_pos0 : nilM (quasithinD4Root 0 true) * nilM (quasithinD4Root 0 true) = 0 := by
  decide +kernel

theorem nil_sq_pos2 : nilM (quasithinD4Root 2 true) * nilM (quasithinD4Root 2 true) = 0 := by
  decide +kernel

theorem nil_sq_pos3 : nilM (quasithinD4Root 3 true) * nilM (quasithinD4Root 3 true) = 0 := by
  decide +kernel

theorem nil_sq_pos1 : nilM (quasithinD4Root 1 true) * nilM (quasithinD4Root 1 true) = 0 := by
  decide +kernel

theorem nil_sq_neg0 : nilM (quasithinD4Root 0 false) * nilM (quasithinD4Root 0 false) = 0 := by
  decide +kernel

theorem nil_sq_neg2 : nilM (quasithinD4Root 2 false) * nilM (quasithinD4Root 2 false) = 0 := by
  decide +kernel

theorem nil_sq_neg3 : nilM (quasithinD4Root 3 false) * nilM (quasithinD4Root 3 false) = 0 := by
  decide +kernel

theorem nil_sq_neg1 : nilM (quasithinD4Root 1 false) * nilM (quasithinD4Root 1 false) = 0 := by
  decide +kernel

theorem nil_comm_pos02 :
    nilM (quasithinD4Root 0 true) * nilM (quasithinD4Root 2 true) =
      nilM (quasithinD4Root 2 true) * nilM (quasithinD4Root 0 true) := by
  decide +kernel

theorem nil_comm_pos03 :
    nilM (quasithinD4Root 0 true) * nilM (quasithinD4Root 3 true) =
      nilM (quasithinD4Root 3 true) * nilM (quasithinD4Root 0 true) := by
  decide +kernel

theorem nil_comm_pos23 :
    nilM (quasithinD4Root 2 true) * nilM (quasithinD4Root 3 true) =
      nilM (quasithinD4Root 3 true) * nilM (quasithinD4Root 2 true) := by
  decide +kernel

theorem nil_comm_neg02 :
    nilM (quasithinD4Root 0 false) * nilM (quasithinD4Root 2 false) =
      nilM (quasithinD4Root 2 false) * nilM (quasithinD4Root 0 false) := by
  decide +kernel

theorem nil_comm_neg03 :
    nilM (quasithinD4Root 0 false) * nilM (quasithinD4Root 3 false) =
      nilM (quasithinD4Root 3 false) * nilM (quasithinD4Root 0 false) := by
  decide +kernel

theorem nil_comm_neg23 :
    nilM (quasithinD4Root 2 false) * nilM (quasithinD4Root 3 false) =
      nilM (quasithinD4Root 3 false) * nilM (quasithinD4Root 2 false) := by
  decide +kernel

theorem mul_three_comm {M : Type*} [Monoid M] {x y z x' y' z' : M} (h1 : y * x' = x' * y)
    (h2 : z * x' = x' * z) (h3 : z * y' = y' * z) :
    x * y * z * (x' * y' * z') = x * x' * (y * y') * (z * z') := by
  have hz : z * (x' * y') = x' * y' * z := by
    rw [← mul_assoc, h2, mul_assoc, h3, ← mul_assoc]
  calc x * y * z * (x' * y' * z') = x * y * (z * (x' * y')) * z' := by simp only [mul_assoc]
    _ = x * y * (x' * y' * z) * z' := by rw [hz]
    _ = x * (y * x') * y' * (z * z') := by simp only [mul_assoc]
    _ = x * (x' * y) * y' * (z * z') := by rw [h1]
    _ = x * x' * (y * y') * (z * z') := by simp only [mul_assoc]

@[expose] def Xm (a : GF64) : Matrix (Fin 8) (Fin 8) GF64 :=
  quasithinRootElt (quasithinD4Root 0 true) a * quasithinRootElt (quasithinD4Root 2 true) (a ^ 4) *
    quasithinRootElt (quasithinD4Root 3 true) (a ^ 16)

@[expose] def Ym (a : GF64) : Matrix (Fin 8) (Fin 8) GF64 :=
  quasithinRootElt (quasithinD4Root 0 false) a *
    quasithinRootElt (quasithinD4Root 2 false) (a ^ 4) *
    quasithinRootElt (quasithinD4Root 3 false) (a ^ 16)

@[expose] def Zm (s : Bool) (c : GF64) : Matrix (Fin 8) (Fin 8) GF64 :=
  quasithinRootElt (quasithinD4Root 1 s) c

theorem add_pow_four (a b : GF64) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  rw [← frobF_apply, ← frobF_apply, ← frobF_apply, map_add]

theorem add_pow_sixteen (a b : GF64) : (a + b) ^ 16 = a ^ 16 + b ^ 16 := by
  have h : ∀ c : GF64, c ^ 16 = (c ^ 4) ^ 4 := fun c => by rw [← pow_mul]
  rw [h, h, h, add_pow_four, add_pow_four]

theorem Xm_add (a b : GF64) : Xm a * Xm b = Xm (a + b) := by
  unfold Xm
  have h1 := root_comm nil_comm_pos02.symm (a ^ 4) b
  have h2 := root_comm nil_comm_pos03.symm (a ^ 16) b
  have h3 := root_comm nil_comm_pos23.symm (a ^ 16) (b ^ 4)
  rw [mul_three_comm h1 h2 h3, root_add nil_sq_pos0, root_add nil_sq_pos2,
    root_add nil_sq_pos3, ← add_pow_four, ← add_pow_sixteen]

theorem Ym_add (a b : GF64) : Ym a * Ym b = Ym (a + b) := by
  unfold Ym
  have h1 := root_comm nil_comm_neg02.symm (a ^ 4) b
  have h2 := root_comm nil_comm_neg03.symm (a ^ 16) b
  have h3 := root_comm nil_comm_neg23.symm (a ^ 16) (b ^ 4)
  rw [mul_three_comm h1 h2 h3, root_add nil_sq_neg0, root_add nil_sq_neg2,
    root_add nil_sq_neg3, ← add_pow_four, ← add_pow_sixteen]

theorem Zm_pos_add (a b : GF64) : Zm true a * Zm true b = Zm true (a + b) :=
  root_add nil_sq_pos1 a b

theorem Zm_neg_add (a b : GF64) : Zm false a * Zm false b = Zm false (a + b) :=
  root_add nil_sq_neg1 a b

theorem Xm_zero : Xm 0 = 1 := by
  simp [Xm, root_zero]

theorem Ym_zero : Ym 0 = 1 := by
  simp [Ym, root_zero]

theorem add_self_eq_zero (a : GF64) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem Xm_mul_self (a : GF64) : Xm a * Xm a = 1 := by
  rw [Xm_add, add_self_eq_zero, Xm_zero]

theorem Ym_mul_self (a : GF64) : Ym a * Ym a = 1 := by
  rw [Ym_add, add_self_eq_zero, Ym_zero]

theorem Zm_mul_self (s : Bool) (c : GF64) : Zm s c * Zm s c = 1 := by
  cases s
  · rw [Zm_neg_add, add_self_eq_zero]; exact root_zero _
  · rw [Zm_pos_add, add_self_eq_zero]; exact root_zero _

@[expose] def wC : GF64 := ⟨GF8.ofNat' 5, GF8.ofNat' 2⟩

@[expose] def wqC : GF64 := ⟨GF8.ofNat' 1, GF8.ofNat' 1⟩

@[expose] def letterMat (k : ℕ) : Matrix (Fin 8) (Fin 8) GF64 :=
  if k < 12 then (if k % 2 = 0 then Xm (wC ^ (k / 2)) else Ym (wC ^ (k / 2)))
  else Zm (decide (k % 2 = 0)) (if k < 14 then 1 else wqC)

theorem letterMat_mul_self (k : ℕ) : letterMat k * letterMat k = 1 := by
  unfold letterMat
  split_ifs
  · exact Xm_mul_self _
  · exact Ym_mul_self _
  · exact Zm_mul_self _ _
  · exact Zm_mul_self _ _

@[expose] def letterGL (k : ℕ) : GL (Fin 8) GF64 :=
  ⟨letterMat k, letterMat k, letterMat_mul_self k, letterMat_mul_self k⟩

@[expose] def wordGL (w : List ℕ) : GL (Fin 8) GF64 := (w.map letterGL).prod

@[expose] def letterTable : Array (Array GF64) :=
  Array.ofFn (n := 16) fun k => ofMat (letterMat k.val)

@[expose] def letterArr (k : ℕ) : Array GF64 := letterTable.getD k oneArr

@[expose] def wordArr (w : List ℕ) : Array GF64 :=
  w.foldr (fun l A => mulArr (letterArr l) A) oneArr

theorem size_letterArr (k : ℕ) : (letterArr k).size = 64 := by
  unfold letterArr
  by_cases hk : k < 16
  · have : letterTable.getD k oneArr = ofMat (letterMat k) := by
      simp [letterTable, Array.getD_eq_getD_getElem?, hk]
    rw [this]; exact size_ofMat _
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp [letterTable]; omega)]
    exact size_oneArr

theorem toMat_letterArr {k : ℕ} (hk : k < 16) : toMat (letterArr k) = letterMat k := by
  have : letterTable.getD k oneArr = ofMat (letterMat k) := by
    simp [letterTable, Array.getD_eq_getD_getElem?, hk]
  rw [letterArr, this, toMat_ofMat]

theorem wordArr_nil : wordArr [] = oneArr := rfl

theorem wordArr_cons (l : ℕ) (w : List ℕ) :
    wordArr (l :: w) = mulArr (letterArr l) (wordArr w) := rfl

theorem size_wordArr (w : List ℕ) : (wordArr w).size = 64 := by
  induction w with
  | nil => rw [wordArr_nil]; exact size_oneArr
  | cons l w ih => rw [wordArr_cons]; exact size_mulArr _ _

theorem coe_wordGL {w : List ℕ} (hw : ∀ l ∈ w, l < 16) :
    ((wordGL w : GL (Fin 8) GF64) : Matrix (Fin 8) (Fin 8) GF64) = toMat (wordArr w) := by
  induction w with
  | nil => rw [wordArr_nil, oneArr, toMat_ofMat]; rfl
  | cons l w ih =>
    have hl : l < 16 := hw l List.mem_cons_self
    show (letterMat l) * ((wordGL w : GL (Fin 8) GF64) : Matrix (Fin 8) (Fin 8) GF64) = _
    rw [ih (fun a ha => hw a (List.mem_cons_of_mem l ha)), wordArr_cons, toMat_mulArr,
      toMat_letterArr hl]

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
