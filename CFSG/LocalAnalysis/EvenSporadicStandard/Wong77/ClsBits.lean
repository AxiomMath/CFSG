module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.Wong77.Cls

open Matrix

abbrev Vec : Type := Fin 11 → ZMod 2

abbrev Mat : Type := Matrix (Fin 11) (Fin 11) (ZMod 2)

@[expose] def e0 : Vec := Pi.single 0 1

@[expose] def comp (a : Vec) : Mat :=
  Matrix.of fun r j => if j.val = 10 then a r else if r.val = j.val + 1 then 1 else 0

@[expose] def kry (M : Mat) (z₀ z₁ : Vec) : Mat :=
  Matrix.of fun r j => if j.val = 0 then z₀ r else ((M ^ (j.val - 1)) *ᵥ z₁) r

@[expose] def phi (U Binv : Mat) (y : Vec) : Mat := kry U e0 y * Binv

@[expose] def wordA (C Y X : Mat) : Mat :=
  X ^ 3 * C * X * C ^ 21 * Y * X ^ 3 * C ^ 22 * X ^ 3 * Y * X ^ 3


@[expose] def toVec (n : ℕ) : Vec := fun i => if n.testBit i.val then 1 else 0

@[expose] def toMat (cols : List ℕ) : Mat := Matrix.of fun r j => toVec (cols.getD j.val 0) r

@[expose] def mvN (cols : List ℕ) (v : ℕ) : ℕ :=
  (List.range 11).foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) 0

@[expose] def mulN (A B : List ℕ) : List ℕ := B.map (mvN A)

@[expose] def oneN : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

@[expose] def powN (A : List ℕ) : ℕ → List ℕ
  | 0 => oneN
  | n + 1 => mulN (powN A n) A

@[expose] def compHead : List ℕ := [2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]

@[expose] def compN (a : ℕ) : List ℕ := compHead ++ [a]

@[expose] def itN (A : List ℕ) (k v : ℕ) : ℕ := (mvN A)^[k] v

@[expose] def kryN (A : List ℕ) (z₀ z₁ : ℕ) : List ℕ :=
  z₀ :: (List.range 10).map fun k => itN A k z₁

@[expose] def eqV (a b : ℕ) : Bool := (List.range 11).all fun k => a.testBit k == b.testBit k

@[expose] def eqM (A B : List ℕ) : Bool :=
  (List.range 11).all fun j => eqV (A.getD j 0) (B.getD j 0)

theorem toVec_xor (a b : ℕ) : toVec (a ^^^ b) = toVec a + toVec b := by
  ext i
  simp only [toVec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i.val <;> cases b.testBit i.val <;> decide

theorem toVec_zero : toVec 0 = 0 := by
  ext i
  simp [toVec]

theorem toVec_one : toVec 1 = e0 := by decide

theorem sum_range_map {α : Type*} [AddCommMonoid α] (g : ℕ → α) (n : ℕ) :
    ((List.range n).map g).sum = ∑ j ∈ Finset.range n, g j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ,
      List.map_singleton, List.sum_singleton]

theorem mvN_foldl (cols : List ℕ) (v : ℕ) (l : List ℕ) (acc : ℕ) :
    toVec (l.foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) acc) =
      toVec acc + (l.map fun j => if v.testBit j then toVec (cols.getD j 0) else 0).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    split_ifs
    · rw [toVec_xor, add_assoc]
    · simp

theorem toVec_mul_ite (b : Bool) (n : ℕ) (r : Fin 11) :
    (if b = true then toVec n else 0) r = toVec n r * (if b = true then 1 else 0) := by
  cases b <;> simp

theorem mvN_eq (cols : List ℕ) (v : ℕ) : toVec (mvN cols v) = toMat cols *ᵥ toVec v := by
  unfold mvN
  rw [mvN_foldl, toVec_zero, zero_add, sum_range_map]
  ext r
  rw [Finset.sum_apply, ← Fin.sum_univ_eq_sum_range (fun j => (if v.testBit j then
    toVec (cols.getD j 0) else 0) r) 11]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => toVec_mul_ite _ _ _

theorem mvN_zero (A : List ℕ) : mvN A 0 = 0 := by
  have : ∀ (l : List ℕ) (acc : ℕ),
      l.foldl (fun acc j => if (0 : ℕ).testBit j then acc ^^^ A.getD j 0 else acc) acc = acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons j l _ => intro acc; simp [List.foldl_cons]
  exact this _ _

theorem mulN_eq (A B : List ℕ) : toMat (mulN A B) = toMat A * toMat B := by
  ext r j
  have h : (B.map (mvN A)).getD j.val 0 = mvN A (B.getD j.val 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases B[j.val]? with
    | none => simp [mvN_zero]
    | some x => simp
  simp only [toMat, mulN, Matrix.of_apply, h, mvN_eq]
  rfl

theorem toMat_oneN : toMat oneN = 1 := by decide

theorem powN_eq (A : List ℕ) (n : ℕ) : toMat (powN A n) = toMat A ^ n := by
  induction n with
  | zero => simp [powN, toMat_oneN]
  | succ n ih => rw [powN, mulN_eq, ih, pow_succ]

theorem toMat_compN (a : ℕ) : toMat (compN a) = comp (toVec a) := by
  have hhead : ∀ j : Fin 11, j.val < 10 → ∀ r : Fin 11,
      toVec (compHead.getD j.val 0) r = if r.val = j.val + 1 then 1 else 0 := by decide
  ext r j
  show toVec ((compHead ++ [a]).getD j.val 0) r = comp (toVec a) r j
  rw [comp, Matrix.of_apply]
  by_cases hj : j.val = 10
  · have : (compHead ++ [a]).getD j.val 0 = a := by
      rw [hj]; simp [compHead]
    rw [this]
    simp only [hj, ↓reduceIte]
  · have hj' : j.val < 10 := by have := j.isLt; omega
    have : (compHead ++ [a]).getD j.val 0 = compHead.getD j.val 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simpa [compHead] using hj')]
    rw [this, hhead j hj' r]
    simp only [hj, ↓reduceIte]

theorem itN_eq (A : List ℕ) (k v : ℕ) : toVec (itN A k v) = (toMat A ^ k) *ᵥ toVec v := by
  induction k generalizing v with
  | zero => simp [itN]
  | succ k ih =>
    rw [itN, Function.iterate_succ_apply, ← itN, ih, mvN_eq, Matrix.mulVec_mulVec, pow_succ]

theorem toMat_kryN (A : List ℕ) (z₀ z₁ : ℕ) :
    toMat (kryN A z₀ z₁) = kry (toMat A) (toVec z₀) (toVec z₁) := by
  ext r j
  show toVec ((kryN A z₀ z₁).getD j.val 0) r = kry (toMat A) (toVec z₀) (toVec z₁) r j
  rw [kry, Matrix.of_apply]
  by_cases hj : j.val = 0
  · simp [kryN, hj]
  · simp only [hj, ↓reduceIte]
    obtain ⟨k, hk⟩ : ∃ k, j.val = k + 1 := ⟨j.val - 1, by omega⟩
    have hk10 : k < 10 := by have := j.isLt; omega
    have : (kryN A z₀ z₁).getD j.val 0 = itN A k z₁ := by
      rw [hk, kryN]
      simp [List.getD_eq_getElem?_getD, hk10]
    rw [this, itN_eq, hk]
    simp

theorem eqV_iff {a b : ℕ} : eqV a b = true ↔ toVec a = toVec b := by
  simp only [eqV, List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · intro h
    ext i
    simp [toVec, h i.val i.isLt]
  · intro h k hk
    have := congrFun h ⟨k, hk⟩
    simp only [toVec] at this
    cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp [ha, hb] at this ⊢

theorem eqM_iff {A B : List ℕ} : eqM A B = true ↔ toMat A = toMat B := by
  simp only [eqM, List.all_eq_true, List.mem_range, eqV_iff]
  constructor
  · intro h
    ext r j
    have := h j.val j.isLt
    simpa [toMat] using congrFun this r
  · intro h j hj
    funext r
    have := congrFun (congrFun h r) ⟨j, hj⟩
    simpa [toMat] using this

theorem exists_lt_toVec (y : Vec) : ∃ n < 2048, toVec n = y := by
  have hinj : Function.Injective fun n : Fin 2048 => toVec n.val := by
    intro n m h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 11
    · have := congrFun h ⟨k, hk⟩
      simp only [toVec] at this
      cases ha : n.val.testBit k <;> cases hb : m.val.testBit k <;> simp [ha, hb] at this ⊢
    · have h1 : n.val < 2 ^ k := lt_of_lt_of_le n.isLt
        (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 11 ≤ k))
      have h2 : m.val < 2 ^ k := lt_of_lt_of_le m.isLt
        (by simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 11 ≤ k))
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
  have hcard : Fintype.card (Fin 2048) = Fintype.card Vec := by simp
  obtain ⟨n, hn⟩ := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩ |>.2 y
  exact ⟨n.val, n.isLt, hn⟩


theorem comp_mulVec_single (a : Vec) (j : Fin 11) (hj : j.val < 10) :
    comp a *ᵥ Pi.single j 1 = Pi.single ⟨j.val + 1, by omega⟩ 1 := by
  rw [Matrix.mulVec_single_one]
  ext r
  have hj10 : j.val ≠ 10 := by omega
  simp [comp, Pi.single_apply, hj10, Fin.ext_iff]

theorem comp_pow_e0_aux (a : Vec) :
    ∀ j : ℕ, ∀ hj : j < 11, (comp a ^ j) *ᵥ e0 = Pi.single ⟨j, hj⟩ 1
  | 0, _ => by rw [pow_zero, Matrix.one_mulVec]; rfl
  | j + 1, hj => by
    rw [pow_succ', ← Matrix.mulVec_mulVec, comp_pow_e0_aux a j (by omega)]
    exact comp_mulVec_single a ⟨j, by omega⟩ (by simp; omega)

theorem comp_pow_e0 (a : Vec) (j : Fin 11) : (comp a ^ j.val) *ᵥ e0 = Pi.single j 1 :=
  comp_pow_e0_aux a j.val j.isLt

theorem comm_pow (Y C : Mat) (h : Y * C = C ^ 16 * Y) (n : ℕ) : Y * C ^ n = (C ^ 16) ^ n * Y := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc Y * C ^ (n + 1) = (Y * C ^ n) * C := by rw [pow_succ, mul_assoc]
      _ = (C ^ 16) ^ n * (Y * C) := by rw [ih, mul_assoc]
      _ = (C ^ 16) ^ (n + 1) * Y := by rw [h, ← mul_assoc, ← pow_succ]

theorem eq_of_fix_comm (a : Vec) {Y Y' : Mat} (h : Y *ᵥ e0 = e0) (h' : Y' *ᵥ e0 = e0)
    (hc : Y * comp a = comp a ^ 16 * Y) (hc' : Y' * comp a = comp a ^ 16 * Y') : Y = Y' := by
  have key : ∀ Z : Mat, Z *ᵥ e0 = e0 → Z * comp a = comp a ^ 16 * Z →
      ∀ j : Fin 11, Z *ᵥ Pi.single j 1 = ((comp a ^ 16) ^ j.val) *ᵥ e0 := by
    intro Z hZ hZc j
    rw [← comp_pow_e0 a j, Matrix.mulVec_mulVec, comm_pow Z (comp a) hZc,
      ← Matrix.mulVec_mulVec, hZ]
  ext r j
  have e1 := congrFun (key Y h hc j) r
  have e2 := congrFun (key Y' h' hc' j) r
  rw [Matrix.mulVec_single_one] at e1 e2
  simp only [Matrix.col_apply] at e1 e2
  rw [e1, e2]

theorem kry_mul {X U U' : Mat} {e e' w : Vec} (hUX : U * X = X * U') (he : X *ᵥ e' = e) :
    X * kry U' e' w = kry U e (X *ᵥ w) := by
  have hpow : ∀ n : ℕ, X * U' ^ n = U ^ n * X := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc X * U' ^ (n + 1) = (X * U' ^ n) * U' := by rw [pow_succ, mul_assoc]
        _ = U ^ n * (X * U') := by rw [ih, mul_assoc]
        _ = U ^ (n + 1) * X := by rw [← hUX, ← mul_assoc, ← pow_succ]
  ext r j
  simp only [Matrix.mul_apply, kry, Matrix.of_apply]
  by_cases hj : j.val = 0
  · simp only [hj, ite_true]
    exact congrFun he r
  · simp only [hj, ite_false]
    show (X *ᵥ (U' ^ (j.val - 1) *ᵥ w)) r = (U ^ (j.val - 1) *ᵥ (X *ᵥ w)) r
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hpow]

theorem eq_phi {X U U' Binv : Mat} {e' w : Vec} (hUX : U * X = X * U') (he : X *ᵥ e' = e0)
    (hB : kry U' e' w * Binv = 1) : X = phi U Binv (X *ᵥ w) := by
  rw [phi, ← kry_mul hUX he, mul_assoc, hB, mul_one]

end CFSG.EvenSporadicStandard.Wong77.Cls
