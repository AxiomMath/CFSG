module

public import CFSG.Certificates.Kernel.Spor.ONLin
public import CFSG.Certificates.Kernel.ONOut.RowsSound
public import Certificates.Data.Kernel.Spor.ONVecK
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.ONKSound

public section

namespace CFSG.KS.ON

open CFSG.KC.Enum CFSG.KS CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.KS.ONOut

@[expose] noncomputable def rowsV (R : Nat → Nat) : Array V :=
  Array.ofFn (n := 154) fun i => vOf (R i.val)

theorem rowsV_size (R : Nat → Nat) : (rowsV R).size = 154 := by
  unfold rowsV
  exact Array.size_ofFn

theorem size_transpose' (d : Nat) (X : Array V) : (transpose d X).size = d := by
  unfold transpose
  exact Array.size_ofFn

theorem size_rowsOf' (d : Nat) (s : String) : (rowsOf d s).size = d := by
  unfold rowsOf
  exact Array.size_ofFn

theorem size_mul' (d : Nat) (X Y : Array V) : (mul d X Y).size = X.size := by
  unfold mul
  exact Array.size_map

theorem arr_ext' {α : Type} [Inhabited α] {n : Nat} {X Y : Array α} (hX : X.size = n)
    (hY : Y.size = n) (h : ∀ i < n, X[i]! = Y[i]!) : X = Y := by
  apply Array.ext (by rw [hX, hY])
  intro i h1 h2
  have hi : i < n := by rw [hX] at h1; exact h1
  have := h i hi
  rwa [getElem!_pos X i h1, getElem!_pos Y i h2] at this

theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] {a : Array α} {f : α → β} {j : Nat}
    (h : j < a.size) : (a.map f)[j]! = f a[j]! := by
  rw [getElem!_pos _ j (by rw [Array.size_map]; exact h), Array.getElem_map, getElem!_pos a j h]

theorem getElem!_ofFn' {α : Type} [Inhabited α] {n : Nat} {f : Fin n → α} {j : Nat} (h : j < n) :
    (Array.ofFn f)[j]! = f ⟨j, h⟩ := by
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact h), Array.getElem_ofFn]

theorem rowsV_get {R : Nat → Nat} {i : Nat} (hi : i < 154) : (rowsV R)[i]! = vOf (R i) := by
  unfold rowsV
  rw [getElem!_ofFn' hi]

theorem V.ext_bits {a b : V} (hp : ∀ t, a.p.testBit t = b.p.testBit t)
    (hm : ∀ t, a.m.testBit t = b.m.testBit t) : a = b := by
  cases a
  cases b
  simp only [V.mk.injEq]
  exact ⟨Nat.eq_of_testBit_eq hp, Nat.eq_of_testBit_eq hm⟩

theorem trEq_spec {X j Y i : Nat} (h : trEq X j Y i = true) :
    (vP X).testBit j = (vP Y).testBit i ∧ (vM X).testBit j = (vM Y).testBit i := by
  unfold trEq at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [bit_testBit, bit_testBit] at h1 h2
  constructor
  · revert h1
    cases (vP X).testBit j <;> cases (vP Y).testBit i <;> decide
  · revert h2
    cases (vM X).testBit j <;> cases (vM Y).testBit i <;> decide

theorem tposK_spec {R C : Nat → Nat} (h : tposK R C = true) :
    (∀ i < 154, canon (R i) = true) ∧ (∀ j < 154, canon (C j) = true) ∧
      ∀ i < 154, ∀ j < 154, (vP (R i)).testBit j = (vP (C j)).testBit i ∧
        (vM (R i)).testBit j = (vM (C j)).testBit i := by
  unfold tposK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  refine ⟨allN_spec h1, allN_spec h2, fun i hi j hj => ?_⟩
  have h4 := allN_spec h3 i hi
  rw [PackFld.strictB_eqP] at h4
  exact trEq_spec (allN_spec h4 j hj)

theorem unitK_spec {L : List Nat} {X : Nat → Nat} (h : unitK L X = true) :
    ∀ k < 154, canon (X k) = true ∧ mv L (X k) = vmk (2 ^ k) 0 := by
  intro k hk
  have h1 := allN_spec h k hk
  rw [PackFld.strictB_eqP] at h1
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h1
  refine ⟨h2, ?_⟩
  rw [Nat.eq_of_beq_eq_true h3, PackFld.shl_eq, Nat.one_mul]

theorem imgK_spec {L : List Nat} {C D : Nat → Nat} (h : imgK L C D = true) :
    ∀ i < 154, canon (D i) = true ∧ mv L (C i) = D i := by
  intro i hi
  have h1 := allN_spec h i hi
  rw [PackFld.strictB_eqP] at h1
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h1
  exact ⟨h2, Nat.eq_of_beq_eq_true h3⟩

theorem sigAt_spec {KS K : Nat → Nat} {LT : List Nat} {i : Nat} (h : sigAt KS K LT i = true) :
    canon (key KS i) = true ∧ key KS i = mv LT (key K i) := by
  unfold sigAt at h
  rw [PackFld.strictB_eqP] at h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨h2, Nat.eq_of_beq_eq_true h3⟩

theorem get_vOf_mod {X : Nat} (hX : canon X = true) (j : Nat) :
    ((vOf X).get j % 3 = 1 ↔ (vP X).testBit j = true) ∧
      ((vOf X).get j % 3 = 2 ↔ (vM X).testBit j = true) := by
  have hw := V.not_both (CFSG.KS.ONLin.wf_vOf hX) j
  unfold V.get
  change ((if (vP X).testBit j then 1 else if (vM X).testBit j then 2 else 0) % 3 = 1 ↔ _) ∧
    ((if (vP X).testBit j then 1 else if (vM X).testBit j then 2 else 0) % 3 = 2 ↔ _)
  change ((vP X).testBit j && (vM X).testBit j) = false at hw
  revert hw
  cases (vP X).testBit j <;> cases (vM X).testBit j <;> decide

theorem transpose_rowsV {R C : Nat → Nat} (h : tposK R C = true) :
    transpose 154 (rowsV R) = rowsV C := by
  obtain ⟨hR, hC, hT⟩ := tposK_spec h
  refine arr_ext' (size_transpose' _ _) (rowsV_size _) fun j hj => ?_
  rw [rowsV_get hj]
  unfold transpose
  rw [getElem!_ofFn' hj]
  have hB := vB_canon (hC j hj)
  apply V.ext_bits
  · intro t
    rw [ofFn_eq_fold, (fold_ofFnStep_bits _ t 154).1]
    by_cases ht : t < 154
    · have e1 : decide (t < 154) = true := decide_eq_true ht
      rw [e1, Bool.true_and, rowsV_get ht]
      have key : (vOf (R t)).get j % 3 = 1 ↔ (vOf (C j)).p.testBit t = true :=
        (get_vOf_mod (hR t ht) j).1.trans (by rw [(hT t ht j hj).1]; exact Iff.rfl)
      exact Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact key)
    · have e1 : decide (t < 154) = false := decide_eq_false ht
      rw [e1, Bool.false_and, (hB t (by omega)).1]
  · intro t
    rw [ofFn_eq_fold, (fold_ofFnStep_bits _ t 154).2]
    by_cases ht : t < 154
    · have e1 : decide (t < 154) = true := decide_eq_true ht
      rw [e1, Bool.true_and, rowsV_get ht]
      have key : (vOf (R t)).get j % 3 = 2 ↔ (vOf (C j)).m.testBit t = true :=
        (get_vOf_mod (hR t ht) j).2.trans (by rw [(hT t ht j hj).2]; exact Iff.rfl)
      exact Bool.eq_iff_iff.2 (by rw [decide_eq_true_iff]; exact key)
    · have e1 : decide (t < 154) = false := decide_eq_false ht
      rw [e1, Bool.false_and, (hB t (by omega)).2]

theorem ofV_inj' {a b : V} (ha : VB 256 a) (hb : VB 256 b) (h : ofV a = ofV b) : a = b := by
  have key : ∀ t, a.p.testBit t = b.p.testBit t ∧ a.m.testBit t = b.m.testBit t := by
    intro t
    by_cases ht : t < 256
    · have h1 := bit_ofV a ht
      have h2 := bit_ofV b ht
      rw [h] at h1
      exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
    · rw [(ha t (by omega)).1, (ha t (by omega)).2, (hb t (by omega)).1, (hb t (by omega)).2]
      exact ⟨rfl, rfl⟩
  exact V.ext_bits (fun t => (key t).1) (fun t => (key t).2)

theorem vB_of_rowC {a : V} (h : RowC 154 a) : VB 256 a := fun i hi => h.2 i (by omega)

theorem colsK_transpose {C : Nat → Nat} {cs : List Char} (h : colsK C cs = true) :
    (∀ j < 154, canon (C j) = true) ∧
      transpose 154 (rowsOf 154 (String.ofList cs)) = rowsV C := by
  have hc : ∀ j < 154, canon (C j) = true := by
    unfold colsK at h
    exact allN_spec ((bAnd_iff _ _).1 h).1
  refine ⟨hc, arr_ext' (size_transpose' _ _) (rowsV_size _) fun j hj => ?_⟩
  rw [rowsV_get hj]
  have := colsK_sound h j hj
  rw [getElem!_map' (by rw [size_transpose']; exact hj)] at this
  exact ofV_inj' (vB_of_rowC (rowC_transpose _ j)) (fun i hi => vB_canon (hc j hj) i (by omega))
    this

theorem canonM_rowsV {R : Nat → Nat} (hR : ∀ i < 154, canon (R i) = true) :
    canonM 154 (rowsV R) = true := by
  refine canonM_of (rowsV_size R) fun i hi => ?_
  rw [rowsV_get hi]
  exact ⟨CFSG.KS.ONLin.wf_vOf (hR i hi), fun j hj => vB_canon (hR i hi) j hj⟩

theorem canonM_transpose (X : Array V) : canonM 154 (transpose 154 X) = true :=
  canonM_of (size_transpose' 154 X) fun i _ => rowC_transpose X i

theorem canonM_rowsOf (s : String) : canonM 154 (rowsOf 154 s) = true := by
  refine canonM_of (size_rowsOf' 154 s) fun i hi => ?_
  unfold rowsOf
  rw [getElem!_ofFn' hi]
  exact rowC_ofFn _ _

theorem transpose_transpose {X : Array V} (hX : canonM 154 X = true) :
    transpose 154 (transpose 154 X) = X :=
  eq_of_canonM (canonM_transpose _) hX (by rw [toMat_transpose, toMat_transpose,
    Matrix.transpose_transpose])

theorem rowsOf_eq {C R : Nat → Nat} {cs : List Char} (h : colsK C cs = true)
    (hT : tposK C R = true) : rowsOf 154 (String.ofList cs) = rowsV R := by
  rw [← transpose_transpose (canonM_rowsOf _), (colsK_transpose h).2, transpose_rowsV hT]

theorem comb_congr' {d : Nat} {Y Y' : Array V} (h : ∀ j < d, Y[j]! = Y'[j]!) (r : V) :
    comb d Y r = comb d Y' r := by
  induction d with
  | zero => simp only [comb, Nat.fold_zero]
  | succ d ih =>
    simp only [comb] at ih ⊢
    rw [Nat.fold_succ, Nat.fold_succ, ih (fun j hj => h j (by omega)), h d (by omega)]

theorem comb_rowsV {C : Nat → Nat} {L : List Nat}
    (hL : L.length = 154 ∧ ∀ j < 154, L.getD j 0 = C j) (hC : ∀ j < 154, canon (C j) = true)
    (X : Nat) : comb 154 (rowsV C) (vOf X) = vOf (mv L X) := by
  rw [vOf_mv (by rw [hL.1]; intro j hj; rw [hL.2 j hj]; exact hC j hj), hL.1]
  exact comb_congr' (fun j hj => by rw [map_vOf_get (by omega), hL.2 j hj, rowsV_get hj]) _

theorem mul_rowsV {X : Array V} {R : Nat → Nat} {C : Nat → Nat} {L : List Nat}
    (hL : L.length = 154 ∧ ∀ j < 154, L.getD j 0 = C j) (hC : ∀ j < 154, canon (C j) = true)
    (hX : X = rowsV R) {D : Nat → Nat} (hD : ∀ i < 154, mv L (R i) = D i) :
    mul 154 X (rowsV C) = rowsV D := by
  subst hX
  refine arr_ext' (by rw [size_mul', rowsV_size]) (rowsV_size _) fun i hi => ?_
  rw [mul_getElem! (by rw [rowsV_size]; exact hi), rowsV_get hi, rowsV_get hi, comb_rowsV hL hC,
    hD i hi]

end CFSG.KS.ON

end
