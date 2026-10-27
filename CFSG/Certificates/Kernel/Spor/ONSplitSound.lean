module

import CFSG.F3.Spec
import CFSG.Certificates.Kernel.Spor.Loops
public import Aesop.BuiltinRules
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.ON.Native
open CFSG.ONSchreier.Native
open scoped Matrix

private theorem VB.ofFn (d : Nat) (f : Nat → Nat) : VB d (V.ofFn d f) := fun i hi => by
  rw [ofFn_eq_fold]
  obtain ⟨h1, h2⟩ := fold_ofFnStep_bits f i d
  rw [h1, h2]
  simp [show ¬ i < d by omega]

private theorem VB.rows_transpose {d : Nat} (X : Array V) : ∀ j : Nat, VB d (transpose d X)[j]! := by
  intro j
  unfold transpose
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact VB.ofFn d _
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact VB.zero d

private theorem VB.rows_rowsOf {d : Nat} (s : String) : ∀ j : Nat, VB d (rowsOf d s)[j]! := by
  intro j
  unfold rowsOf
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact VB.ofFn d _
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact VB.zero d

private theorem VB.rows_mul {d : Nat} {X Y : Array V} (hY : ∀ j : Nat, VB d Y[j]!) :
    ∀ j : Nat, VB d (mul d X Y)[j]! := by
  intro j
  by_cases hj : j < X.size
  · rw [mul_getElem! hj]
    exact VB.comb _ fun k _ => hY k
  · rw [getElem!_neg _ j (by simpa [CFSG.F3.Native.mul] using hj)]
    exact VB.zero d

private theorem VB.rows_idM (d : Nat) : ∀ j : Nat, VB d (idM d)[j]! := by
  intro j
  unfold idM
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    intro i hi
    refine ⟨?_, Nat.zero_testBit i⟩
    dsimp only
    rw [testBit_one_shiftLeft]
    exact decide_eq_false (by omega)
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact VB.zero d

private theorem bits_of_val {a b : V} (ha : a.wf = true) (hb : b.wf = true) {k : Nat}
    (h : a.val k = b.val k) : a.p.testBit k = b.p.testBit k ∧ a.m.testBit k = b.m.testBit k := by
  rw [V.val_eq_bitVal, V.val_eq_bitVal] at h
  have h1 := V.not_both ha k
  have h2 := V.not_both hb k
  revert h h1 h2
  cases a.p.testBit k <;> cases a.m.testBit k <;> cases b.p.testBit k <;> cases b.m.testBit k <;>
    decide

private theorem V.eq_of {a b : V} (hp : a.p = b.p) (hm : a.m = b.m) : a = b := by
  cases a
  cases b
  simp only at hp hm
  rw [hp, hm]

private theorem eqM_of_toMat {d : Nat} {X Y : Array V} (hX : X.size = d) (hY : Y.size = d)
    (wX : RowsWF X) (wY : RowsWF Y) (bX : ∀ j : Nat, VB d X[j]!) (bY : ∀ j : Nat, VB d Y[j]!)
    (h : toMat d X = toMat d Y) : eqM d X Y = true := by
  unfold eqM
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hX, hY⟩, ?_⟩
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro i _
  have hv : ∀ k, X[i.val]!.p.testBit k = Y[i.val]!.p.testBit k ∧
      X[i.val]!.m.testBit k = Y[i.val]!.m.testBit k := by
    intro k
    by_cases hk : k < d
    · have := congrFun (congrFun h i) ⟨k, hk⟩
      rw [toMat_apply, toMat_apply] at this
      exact bits_of_val (wX i) (wY i) this
    · rw [(bX i k (by omega)).1, (bX i k (by omega)).2, (bY i k (by omega)).1,
        (bY i k (by omega)).2]
      exact ⟨rfl, rfl⟩
  exact V.beq_iff.2 ⟨Nat.eq_of_testBit_eq fun k => (hv k).1, Nat.eq_of_testBit_eq fun k => (hv k).2⟩

private theorem toMat_congr {d : Nat} {X Y : Array V} (h : ∀ i < d, X[i]! = Y[i]!) :
    toMat d X = toMat d Y := by
  ext i j
  rw [toMat_apply, toMat_apply, h i i.isLt]

private theorem comb_congr {d : Nat} {Y Y' : Array V} (h : ∀ j < d, Y[j]! = Y'[j]!) (r : V) :
    comb d Y r = comb d Y' r := by
  induction d with
  | zero => simp only [CFSG.F3.Native.comb, Nat.fold_zero]
  | succ d ih =>
    simp only [CFSG.F3.Native.comb] at ih ⊢
    rw [Nat.fold_succ, Nat.fold_succ, ih (fun j hj => h j (by omega)), h d (by omega)]

private theorem ofV_inj {a b : V} (ha : VB 256 a) (hb : VB 256 b) (h : ofV a = ofV b) : a = b := by
  have key : ∀ t, a.p.testBit t = b.p.testBit t ∧ a.m.testBit t = b.m.testBit t := by
    intro t
    by_cases ht : t < 256
    · have h1 := bit_ofV a ht
      have h2 := bit_ofV b ht
      rw [h] at h1
      exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
    · rw [(ha t (by omega)).1, (ha t (by omega)).2, (hb t (by omega)).1, (hb t (by omega)).2]
      exact ⟨rfl, rfl⟩
  exact V.eq_of (Nat.eq_of_testBit_eq fun t => (key t).1) (Nat.eq_of_testBit_eq fun t => (key t).2)

private theorem cols_eq {cs : List Char} {C : Nat → Nat} (h : colsK C cs = true) :
    (∀ j < 154, canon (C j) = true) ∧
      ∀ j < 154, (transpose 154 (rowsOf 154 (String.ofList cs)))[j]! = vOf (C j) := by
  have hc : ∀ j < 154, canon (C j) = true := by
    unfold colsK at h
    rw [bAnd_iff] at h
    exact allN_spec h.1
  refine ⟨hc, fun j hj => ?_⟩
  have := colsK_sound h j hj
  rw [getElem!_pos _ j (by simp [transpose, hj]), Array.getElem_map,
    ← getElem!_pos _ j (by simp [transpose, hj])] at this
  exact ofV_inj (fun i hi => VB.rows_transpose _ j i (by omega))
    (fun i hi => vB_canon (hc j hj) i (by omega)) this

private theorem vOf_mv_cols {cs : List Char} {C : Nat → Nat} {L : List Nat}
    (h : colsK C cs = true) (hL : L.length = 154 ∧ ∀ j < 154, L.getD j 0 = C j) (X : Nat) :
    vOf (mv L X) = comb 154 (transpose 154 (rowsOf 154 (String.ofList cs))) (vOf X) := by
  obtain ⟨hc, hcol⟩ := cols_eq h
  rw [vOf_mv (by rw [hL.1]; intro j hj; rw [hL.2 j hj]; exact hc j hj), hL.1]
  exact comb_congr (fun j hj => by rw [map_vOf_get (by omega), hL.2 j hj, hcol j hj]) _

private theorem toMat_powM {d : Nat} {M : Array V} (hM : RowsWF M) (bM : ∀ j : Nat, VB d M[j]!) :
    ∀ e, (powM d M e).size = d ∧ RowsWF (powM d M e) ∧ (∀ j : Nat, VB d (powM d M e)[j]!) ∧
      toMat d (powM d M e) = toMat d M ^ e
  | 0 => ⟨by simp [powM, idM], RowsWF.idM d, VB.rows_idM d, by rw [powM, toMat_idM, pow_zero]⟩
  | e + 1 => by
    obtain ⟨h1, h2, -, h4⟩ := toMat_powM hM bM e
    refine ⟨by simp [powM, CFSG.F3.Native.mul, h1], RowsWF.mul _ d h2 hM, ?_, ?_⟩
    · rw [powM]
      exact VB.rows_mul bM
    · rw [powM, toMat_mul h1 h2 hM, h4, pow_succ]

private theorem vOf_e (j : Nat) (hj : j < 154) : vOf (vmk (2 ^ j) 0) = (idM 154)[j]! := by
  rw [vOf_vmk (Nat.pow_lt_pow_right (by omega) (by omega))]
  unfold idM
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn, Nat.one_shiftLeft]

private theorem size_transpose (d : Nat) (X : Array V) : (transpose d X).size = d := by
  simp [transpose]

private theorem size_mul (d : Nat) (X Y : Array V) : (mul d X Y).size = X.size := by
  simp [CFSG.F3.Native.mul]

private theorem size_idM (d : Nat) : (idM d).size = d := by simp [idM]

private theorem sq_of_cols {R : Array V} {C : Nat → Nat} {L : List Nat} (sR : R.size = 154)
    (wR : RowsWF R) (bR : ∀ j : Nat, VB 154 R[j]!)
    (hcol : ∀ j < 154, (transpose 154 R)[j]! = vOf (C j))
    (hmv : ∀ X, vOf (mv L X) = comb 154 (transpose 154 R) (vOf X))
    (h2 : ∀ j < 154, mv L (C j) = vmk (2 ^ j) 0) : eqM 154 (mul 154 R R) (idM 154) = true := by
  have wT := RowsWF.transpose 154 R
  have hrow : ∀ j < 154, (mul 154 (transpose 154 R) (transpose 154 R))[j]! = (idM 154)[j]! := by
    intro j hj
    rw [mul_getElem! (X := transpose 154 R) (by rw [size_transpose]; exact hj), ← vOf_e j hj,
      ← h2 j hj, hmv, hcol j hj]
  have hT := toMat_congr hrow
  rw [toMat_mul (size_transpose _ R) wT wT, toMat_transpose, toMat_idM] at hT
  refine eqM_of_toMat (by rw [size_mul, sR]) (size_idM _) (RowsWF.mul _ _ wR wR) (RowsWF.idM _)
    (VB.rows_mul bR) (VB.rows_idM _) ?_
  rw [toMat_mul sR wR wR, toMat_idM, ← Matrix.transpose_transpose (toMat 154 R * toMat 154 R),
    Matrix.transpose_mul, hT, Matrix.transpose_one]

private theorem pow4_of_cols {R : Array V} {C : Nat → Nat} {L : List Nat}
    (wR : RowsWF R) (bR : ∀ j : Nat, VB 154 R[j]!)
    (hcol : ∀ j < 154, (transpose 154 R)[j]! = vOf (C j))
    (hmv : ∀ X, vOf (mv L X) = comb 154 (transpose 154 R) (vOf X))
    (h4 : ∀ j < 154, mv L (mv L (mv L (C j))) = vmk (2 ^ j) 0) :
    eqM 154 (powM 154 R 4) (idM 154) = true := by
  have wT := RowsWF.transpose 154 R
  have sT := size_transpose 154 R
  have hrow : ∀ j < 154, (mul 154 (mul 154 (mul 154 (transpose 154 R) (transpose 154 R))
      (transpose 154 R)) (transpose 154 R))[j]! = (idM 154)[j]! := by
    intro j hj
    rw [mul_getElem! (X := mul 154 (mul 154 (transpose 154 R) (transpose 154 R)) (transpose 154 R))
        (by rw [size_mul, size_mul, sT]; exact hj),
      mul_getElem! (X := mul 154 (transpose 154 R) (transpose 154 R)) (by rw [size_mul, sT]; exact hj),
      mul_getElem! (X := transpose 154 R) (by rw [sT]; exact hj), ← vOf_e j hj, ← h4 j hj, hmv, hmv,
      hmv, hcol j hj]
  have hT := toMat_congr hrow
  rw [toMat_mul (by rw [size_mul, size_mul, sT]) (RowsWF.mul _ _ (RowsWF.mul _ _ wT wT) wT) wT,
    toMat_mul (by rw [size_mul, sT]) (RowsWF.mul _ _ wT wT) wT,
    toMat_mul sT wT wT, toMat_transpose, toMat_idM] at hT
  obtain ⟨p1, p2, p3, p4⟩ := toMat_powM (d := 154) wR bR 4
  refine eqM_of_toMat p1 (size_idM _) p2 (RowsWF.idM _) p3 (VB.rows_idM _) ?_
  have e4 : (toMat 154 R)ᵀ ^ 4 =
      (toMat 154 R)ᵀ * (toMat 154 R)ᵀ * (toMat 154 R)ᵀ * (toMat 154 R)ᵀ := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  rw [p4, toMat_idM, ← Matrix.transpose_transpose (toMat 154 R ^ 4), Matrix.transpose_pow, e4, hT,
    Matrix.transpose_one]

theorem matrixK_sound {csA csB : List Char} {CA CB : Nat → Nat} {LA LB : List Nat}
    (hA : colsK CA csA = true) (hB : colsK CB csB = true)
    (hLA : LA.length = 154 ∧ ∀ j < 154, LA.getD j 0 = CA j)
    (hLB : LB.length = 154 ∧ ∀ j < 154, LB.getD j 0 = CB j)
    (h2 : ∀ j < 154, mv LA (CA j) = vmk (2 ^ j) 0)
    (h4 : ∀ j < 154, mv LB (mv LB (mv LB (CB j))) = vmk (2 ^ j) 0) :
    eqM 154 (mul 154 (rowsOf 154 (String.ofList csA)) (rowsOf 154 (String.ofList csA))) (idM 154) = true ∧
      eqM 154 (powM 154 (rowsOf 154 (String.ofList csB)) 4) (idM 154) = true :=
  ⟨sq_of_cols (by simp [rowsOf]) (RowsWF.rowsOf _ _) (VB.rows_rowsOf _) (cols_eq hA).2
      (vOf_mv_cols hA hLA) h2,
    pow4_of_cols (RowsWF.rowsOf _ _) (VB.rows_rowsOf _) (cols_eq hB).2 (vOf_mv_cols hB hLB) h4⟩

private theorem indexOf_get {keys : Array W}
    (hd : ∀ a < keys.size, ∀ b < keys.size, keys[a]! = keys[b]! → a = b) :
    ∀ i < keys.size, (indexOf keys)[keys[i]!]? = some i := by
  intro i hi
  have key : ∀ m ≤ keys.size, ((List.range m).foldl (fun mp k => mp.insert keys[k]! k)
      (∅ : Std.HashMap W Nat))[keys[i]!]? = if i < m then some i else none := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Std.HashMap.getElem?_insert, ih (by omega)]
      by_cases e : m = i
      · subst e
        simp
      · have : (keys[m]! == keys[i]!) = false := by
          rw [beq_eq_false_iff_ne]
          exact fun h => e (hd m (by omega) i hi h)
        rw [this]
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : i < m
        · have h2 : i < m + 1 := by omega
          simp only [h1, h2, ↓reduceIte]
        · have h2 : ¬ i < m + 1 := by omega
          simp only [h1, h2, ↓reduceIte]
  have := key keys.size (Nat.le_refl _)
  rw [ite_eq_left hi] at this
  exact this

theorem index_sound {keys : Array W} {n : Nat} {K SO SOI : Nat → Nat}
    (hk : keys = Array.ofFn (n := n) fun i => wOfK (key K i.val))
    (hc : ∀ i < n, canon (key K i) = true) (hs : ∀ i < n, sortAt K SO SOI n i = true) :
    ∀ i < n, ∀ d, (indexOf keys).getD keys[i]! d = i := by
  have hsz : keys.size = n := by rw [hk, Array.size_ofFn]
  have hget : ∀ i < n, keys[i]! = wOfK (key K i) := fun i hi => by
    rw [getElem!_pos keys i (by rw [hsz]; exact hi)]
    simp [hk]
  intro i hi d
  rw [Std.HashMap.getD_eq_getD_getElem?,
    indexOf_get (fun a ha b hb e => ?_) i (by rw [hsz]; exact hi)]
  · rfl
  · rw [hsz] at ha hb
    rw [hget a ha, hget b hb] at e
    exact sort_distinct hs a ha b hb (wOfK_inj (hc a ha) (hc b hb) e)

private theorem parAll_true {n chunks : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    CFSG.Sporadic.Th.Native.parAll n chunks p = true := by
  unfold CFSG.Sporadic.Th.Native.parAll
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  change CFSG.Sporadic.Th.Native.allStep j (chunks + 1) n p = true
  unfold CFSG.Sporadic.Th.Native.allStep
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro ⟨k, hk⟩ _
  have hc : 0 < chunks + 1 := Nat.succ_pos _
  have h1 := (Nat.le_div_iff_mul_le hc).1 (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul, Nat.mul_comm] at h1
  exact h _ (by omega)

theorem orbitOK_sound {cA cB : Array W} {root : W} {n SL NS : Nat}
    {K A B SO SOI NX : Nat → Nat} {LA LB : List Nat}
    (hcA : cA.size = 154 ∧ LA.length = 154 ∧ ∀ j < 154, cA[j]! = wOfK (LA.getD j 0))
    (hcB : cB.size = 154 ∧ LB.length = 154 ∧ ∀ j < 154, cB[j]! = wOfK (LB.getD j 0))
    (hCA : ∀ j < 154, canon (LA.getD j 0) = true) (hCB : ∀ j < 154, canon (LB.getD j 0) = true)
    (hr : root = wOfK (key K 0)) (hn : 0 < n ∧ n < 2 ^ 18)
    (hmv : ∀ h < n, mvAt K LA LB A B n h = true)
    (hNS : NS * SL = n) (hX0 : NX 0 = 1) (hXN : NX NS = n)
    (hord : ∀ s < NS, Nat.beq (ordRun A B (s * SL) SL (NX s)) (NX (s + 1)) = true)
    (hsort : ∀ i < n, sortAt K SO SOI n i = true) (chunks : Nat) :
    orbitOK n cA cB (orbitBFS cA cB root n)
      (fun x => (indexOf (orbitBFS cA cB root n).keys).getD x n) chunks = true := by
  obtain ⟨hk, ha, hb⟩ := bfsK_sim hcA hcB hCA hCB hr hn hmv hNS hX0 hXN hord hsort
  have hm := fun h hh => mvAt_spec (hmv h hh)
  generalize orbitBFS cA cB root n = O at hk ha hb ⊢
  have hks : O.keys.size = n := by rw [hk, Array.size_ofFn]
  have has : O.alpha.size = n := by
    have := congrArg Array.size ha
    simpa [natTab, tabArr] using this
  have hbs : O.beta.size = n := by
    have := congrArg Array.size hb
    simpa [natTab, tabArr] using this
  have hget : ∀ i < n, O.keys[i]! = wOfK (key K i) := fun i hi => by
    rw [getElem!_pos _ i (by rw [hks]; exact hi)]
    simp [hk]
  have hap : ∀ (t : CFSG.Sporadic.Th.Native.Table) (T : Nat → Nat), natTab t = tabArr T n →
      ∀ i < n, CFSG.Sporadic.Th.Native.ap t i = tab T i := fun t T e i hi => by
    have := congrArg (fun x => x[i]!) e
    have hts : t.size = n := by simpa [natTab, tabArr] using congrArg Array.size e
    rw [getElem!_pos _ i (by simp [natTab, hts, hi]), getElem!_pos _ i (by simp [tabArr, hi])] at this
    simp only [natTab, tabArr, Array.getElem_map, Array.getElem_ofFn] at this
    unfold CFSG.Sporadic.Th.Native.ap
    rw [getElem!_pos _ i (by rw [hts]; exact hi)]
    exact this
  unfold orbitOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hks, has⟩, hbs⟩, parAll_true fun i hi => ?_⟩
  unfold orbitCheckAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  rw [hget i hi, hap _ _ ha i hi, hap _ _ hb i hi, hget _ (hm i hi).2.1, hget _ (hm i hi).2.2.1,
    mv_sound hcA hCA (hm i hi).1, mv_sound hcB hCB (hm i hi).1, (hm i hi).2.2.2.1,
    (hm i hi).2.2.2.2]
  refine ⟨⟨⟨⟨⟨canon_sound (hm i hi).1, ?_⟩, (hm i hi).2.1⟩, rfl⟩, (hm i hi).2.2.1⟩, rfl⟩
  have := index_sound hk (fun i hi => (hm i hi).1) hsort i hi n
  rw [hget i hi] at this
  exact this

theorem wOfK_vneg {X : Nat} (h : canon X = true) : (wOfK X).neg = wOfK (vneg X) := by
  obtain ⟨-, -, hm⟩ := canon_bits h
  have hm' : vM X < 2 ^ 256 := Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega))
  unfold wOfK
  rw [vneg, vP_vmk hm', vM_vmk hm']
  rfl

theorem wOfK_vmk {p m : Nat} (hp : p < 2 ^ 256) (hm : m < 2 ^ 256) : ofV ⟨p, m⟩ = wOfK (vmk p m) := by
  have _ := hm
  unfold wOfK
  rw [vP_vmk hp, vM_vmk hp]

end CFSG.KS.ON

end
