module

public import Certificates.Data.CFSGNative.F3.Basic
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.F3.Native

@[expose] def V.val (a : V) (j : ℕ) : ZMod 3 := (a.get j : ZMod 3)

@[expose] def toMat (d : ℕ) (X : Array V) : Matrix (Fin d) (Fin d) (ZMod 3) :=
  Matrix.of fun i j => X[i.val]!.val j.val

theorem toMat_apply (d : ℕ) (X : Array V) (i j : Fin d) : toMat d X i j = X[i.val]!.val j.val :=
  rfl

@[expose] def bitVal (p m : Bool) : ZMod 3 := if p then 1 else if m then 2 else 0

theorem V.val_eq_bitVal (a : V) (j : ℕ) : a.val j = bitVal (a.p.testBit j) (a.m.testBit j) := by
  unfold V.val V.get bitVal
  split_ifs <;> simp

theorem V.not_both {a : V} (h : a.wf = true) (j : ℕ) :
    (a.p.testBit j && a.m.testBit j) = false := by
  unfold V.wf at h
  rw [beq_iff_eq] at h
  rw [← Nat.testBit_and, h, Nat.zero_testBit]

theorem V.wf_of_bits {a : V} (h : ∀ j, (a.p.testBit j && a.m.testBit j) = false) :
    a.wf = true := by
  unfold V.wf
  rw [beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.zero_testBit, h j]

theorem V.val_zero (j : ℕ) : V.zero.val j = 0 := by
  rw [V.val_eq_bitVal]; simp [V.zero, bitVal]

theorem V.wf_zero : V.zero.wf = true := by decide

private theorem neg_table : ∀ p m : Bool, (p && m) = false → bitVal m p = -bitVal p m := by
  decide

theorem V.val_neg (a : V) (j : ℕ) (h : a.wf = true) : a.neg.val j = -a.val j := by
  rw [V.val_eq_bitVal, V.val_eq_bitVal]
  exact neg_table _ _ (V.not_both h j)

theorem V.wf_neg {a : V} (h : a.wf = true) : a.neg.wf = true := by
  apply V.wf_of_bits
  intro j
  have := V.not_both h j
  simp only [V.neg]
  rw [Bool.and_comm]
  exact this

theorem V.add_bits (a b : V) (j : ℕ) :
    (a.add b).p.testBit j = ((a.p.testBit j && !(b.p.testBit j || b.m.testBit j)) ||
        (b.p.testBit j && !(a.p.testBit j || a.m.testBit j)) || (a.m.testBit j && b.m.testBit j)) ∧
      (a.add b).m.testBit j = ((a.m.testBit j && !(b.p.testBit j || b.m.testBit j)) ||
        (b.m.testBit j && !(a.p.testBit j || a.m.testBit j)) ||
        (a.p.testBit j && b.p.testBit j)) := by
  simp only [V.add, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  constructor <;>
  cases a.p.testBit j <;> cases a.m.testBit j <;> cases b.p.testBit j <;> cases b.m.testBit j <;>
    rfl

private theorem add_table : ∀ ap am bp bm : Bool, (ap && am) = false → (bp && bm) = false →
    bitVal ((ap && !(bp || bm)) || (bp && !(ap || am)) || (am && bm))
      ((am && !(bp || bm)) || (bm && !(ap || am)) || (ap && bp)) = bitVal ap am + bitVal bp bm ∧
    (((ap && !(bp || bm)) || (bp && !(ap || am)) || (am && bm)) &&
      ((am && !(bp || bm)) || (bm && !(ap || am)) || (ap && bp))) = false := by
  decide

theorem V.val_add {a b : V} (ha : a.wf = true) (hb : b.wf = true) (j : ℕ) :
    (a.add b).val j = a.val j + b.val j := by
  obtain ⟨hp, hm⟩ := V.add_bits a b j
  rw [V.val_eq_bitVal, V.val_eq_bitVal, V.val_eq_bitVal, hp, hm]
  exact (add_table _ _ _ _ (V.not_both ha j) (V.not_both hb j)).1

theorem V.wf_add {a b : V} (ha : a.wf = true) (hb : b.wf = true) : (a.add b).wf = true := by
  apply V.wf_of_bits
  intro j
  obtain ⟨hp, hm⟩ := V.add_bits a b j
  rw [hp, hm]
  exact (add_table _ _ _ _ (V.not_both ha j) (V.not_both hb j)).2

theorem V.val_sub {a b : V} (ha : a.wf = true) (hb : b.wf = true) (j : ℕ) :
    (a.sub b).val j = a.val j - b.val j := by
  unfold V.sub
  rw [V.val_add ha (V.wf_neg hb), V.val_neg b j hb]
  exact (sub_eq_add_neg _ _).symm

theorem V.wf_sub {a b : V} (ha : a.wf = true) (hb : b.wf = true) : (a.sub b).wf = true :=
  V.wf_add ha (V.wf_neg hb)

theorem V.beq_iff {a b : V} : a.beq b = true ↔ a.p = b.p ∧ a.m = b.m := by
  simp [V.beq]

theorem testBit_one_shiftLeft (i j : ℕ) : (1 <<< j).testBit i = decide (i = j) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : i = j <;> simp [h, eq_comm]

@[expose] def ofFnStep (f : ℕ → ℕ) (j : ℕ) (v : V) : V :=
  if f j % 3 = 1 then ⟨v.p ||| (1 <<< j), v.m⟩
  else if f j % 3 = 2 then ⟨v.p, v.m ||| (1 <<< j)⟩ else v

theorem ofFn_eq_fold (d : ℕ) (f : ℕ → ℕ) :
    V.ofFn d f = Nat.fold d (fun j _ v => ofFnStep f j v) V.zero := rfl

theorem ofFnStep_bits (f : ℕ → ℕ) (j i : ℕ) (v : V) :
    (ofFnStep f j v).p.testBit i = (v.p.testBit i || (decide (i = j) && decide (f j % 3 = 1))) ∧
      (ofFnStep f j v).m.testBit i =
        (v.m.testBit i || (decide (i = j) && decide (f j % 3 = 2))) := by
  unfold ofFnStep
  split_ifs with h1 h2
  · simp only [Nat.testBit_or, testBit_one_shiftLeft]
    simp [h1]
  · simp only [Nat.testBit_or, testBit_one_shiftLeft]
    simp [h2]
  · simp [h1, h2]

theorem fold_ofFnStep_bits (f : ℕ → ℕ) (i : ℕ) : ∀ n : ℕ,
    (Nat.fold n (fun j _ v => ofFnStep f j v) V.zero).p.testBit i =
        (decide (i < n) && decide (f i % 3 = 1)) ∧
      (Nat.fold n (fun j _ v => ofFnStep f j v) V.zero).m.testBit i =
        (decide (i < n) && decide (f i % 3 = 2)) := by
  intro n
  induction n with
  | zero => simp [V.zero]
  | succ n ih =>
    rw [Nat.fold_succ]
    obtain ⟨h1, h2⟩ := ofFnStep_bits f n i (Nat.fold n (fun j _ v => ofFnStep f j v) V.zero)
    rw [h1, h2, ih.1, ih.2]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · have h' : i ≠ n := by omega
      have h'' : i < n + 1 := by omega
      simp [h, h', h'']
    · simp
    · have h' : ¬ i < n := by omega
      have h'' : ¬ i < n + 1 := by omega
      have h3 : i ≠ n := by omega
      simp [h', h'', h3]

theorem V.val_ofFn (d : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (V.ofFn d f).val j = if j < d then (f j : ZMod 3) else 0 := by
  rw [V.val_eq_bitVal, ofFn_eq_fold]
  obtain ⟨h1, h2⟩ := fold_ofFnStep_bits f j d
  rw [h1, h2]
  unfold bitVal
  by_cases hj : j < d
  · simp only [hj, decide_true, Bool.true_and, ite_true]
    rw [← ZMod.natCast_mod (f j) 3]
    have : f j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : f j % 3 <;> simp
  · simp [hj]

theorem V.wf_ofFn (d : ℕ) (f : ℕ → ℕ) : (V.ofFn d f).wf = true := by
  apply V.wf_of_bits
  intro j
  rw [ofFn_eq_fold]
  obtain ⟨h1, h2⟩ := fold_ofFnStep_bits f j d
  rw [h1, h2]
  by_cases h : f j % 3 = 1 <;> simp [h]

theorem V.val_ext {a b : V} (h : a.beq b = true) (j : ℕ) : a.val j = b.val j := by
  obtain ⟨hp, hm⟩ := V.beq_iff.1 h
  rw [V.val_eq_bitVal, V.val_eq_bitVal, hp, hm]

@[expose] def combStep (Y : Array V) (r : V) (j : ℕ) (acc : V) : V :=
  if r.p.testBit j then acc.add Y[j]! else if r.m.testBit j then acc.sub Y[j]! else acc

theorem comb_eq_fold (d : ℕ) (Y : Array V) (r : V) :
    comb d Y r = Nat.fold d (fun j _ acc => combStep Y r j acc) V.zero := rfl

theorem combStep_spec (Y : Array V) (r : V) (hY : ∀ j : ℕ, Y[j]!.wf = true) (hr : r.wf = true)
    (j k : ℕ) {acc : V} (hacc : acc.wf = true) :
    (combStep Y r j acc).wf = true ∧
      (combStep Y r j acc).val k = acc.val k + r.val j * Y[j]!.val k := by
  have hn := V.not_both hr j
  unfold combStep
  rw [V.val_eq_bitVal r j]
  split_ifs with hp hm
  · refine ⟨V.wf_add hacc (hY j), ?_⟩
    rw [V.val_add hacc (hY j), hp]
    simp [bitVal]
  · refine ⟨V.wf_sub hacc (hY j), ?_⟩
    rw [V.val_sub hacc (hY j)]
    simp only [Bool.not_eq_true] at hp
    simp only [hp, hm, bitVal, Bool.false_eq_true, ite_false, ite_true]
    have key : ∀ x y : ZMod 3, x - y = x + 2 * y := by decide
    exact key _ _
  · refine ⟨hacc, ?_⟩
    simp only [Bool.not_eq_true] at hp hm
    simp [hp, hm, bitVal]

theorem fold_combStep (Y : Array V) (r : V) (hY : ∀ j : ℕ, Y[j]!.wf = true) (hr : r.wf = true)
    (k : ℕ) : ∀ n : ℕ, (Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero).wf = true ∧
      (Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero).val k =
        ∑ j ∈ Finset.range n, r.val j * Y[j]!.val k := by
  intro n
  induction n with
  | zero => simp [V.wf_zero, V.val_zero]
  | succ n ih =>
    rw [Nat.fold_succ, Finset.sum_range_succ]
    obtain ⟨hw, hv⟩ := ih
    obtain ⟨h1, h2⟩ := combStep_spec Y r hY hr n k hw
    exact ⟨h1, by rw [h2, hv]⟩

theorem V.wf_comb (d : ℕ) (Y : Array V) (r : V) (hY : ∀ j : ℕ, Y[j]!.wf = true) (hr : r.wf = true) :
    (comb d Y r).wf = true := (fold_combStep Y r hY hr 0 d).1

theorem V.val_comb (d : ℕ) (Y : Array V) (r : V) (hY : ∀ j : ℕ, Y[j]!.wf = true)
    (hr : r.wf = true) (k : ℕ) :
    (comb d Y r).val k = ∑ j ∈ Finset.range d, r.val j * Y[j]!.val k :=
  (fold_combStep Y r hY hr k d).2

@[expose] def RowsWF (X : Array V) : Prop := ∀ j : ℕ, X[j]!.wf = true

theorem rowsWF_of_wfM {X : Array V} (h : wfM X = true) : RowsWF X := by
  intro j
  unfold wfM at h
  rw [Array.all_eq_true] at h
  by_cases hj : j < X.size
  · rw [getElem!_pos X j hj]; exact h j hj
  · rw [getElem!_neg X j hj]; exact V.wf_zero

theorem RowsWF.mul (X : Array V) {Y : Array V} (d : ℕ) (hX : RowsWF X) (hY : RowsWF Y) :
    RowsWF (mul d X Y) := by
  intro j
  unfold Native.mul
  by_cases hj : j < X.size
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_map]
    have := hX j
    rw [getElem!_pos X j hj] at this
    exact V.wf_comb d Y _ hY this
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

theorem mul_getElem! {d : ℕ} {X Y : Array V} {i : ℕ} (hi : i < X.size) :
    (mul d X Y)[i]! = comb d Y X[i]! := by
  unfold mul
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos X i hi]

theorem toMat_mul {d : ℕ} {X Y : Array V} (hXs : X.size = d) (hX : RowsWF X) (hY : RowsWF Y) :
    toMat d (mul d X Y) = toMat d X * toMat d Y := by
  ext i k
  rw [Matrix.mul_apply, toMat_apply, mul_getElem! (by rw [hXs]; exact i.isLt),
    V.val_comb d Y _ hY (hX i) k, Finset.sum_range (fun j => X[i.val]!.val j * Y[j]!.val k.val)]
  rfl

theorem toMat_idM (d : ℕ) : toMat d (idM d) = 1 := by
  ext i j
  rw [toMat_apply, Matrix.one_apply]
  unfold idM
  rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn, V.val_eq_bitVal]
  simp only [testBit_one_shiftLeft, Nat.zero_testBit, bitVal]
  by_cases h : i = j
  · subst h; simp
  · have h' : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem RowsWF.idM (d : ℕ) : RowsWF (idM d) := by
  intro j
  unfold Native.idM
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    apply V.wf_of_bits
    intro k
    simp
  · rw [getElem!_neg _ j (by simpa using hj)]
    exact V.wf_zero

theorem toMat_transpose {d : ℕ} (X : Array V) :
    toMat d (transpose d X) = Matrix.transpose (toMat d X) := by
  ext j i
  rw [Matrix.transpose_apply, toMat_apply, toMat_apply]
  unfold transpose
  rw [getElem!_pos _ j.val (by simp), Array.getElem_ofFn, V.val_ofFn, ite_eq_left i.isLt]
  unfold V.val
  rfl

theorem RowsWF.transpose (d : ℕ) (X : Array V) : RowsWF (transpose d X) := by
  intro j
  unfold Native.transpose
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact V.wf_ofFn _ _
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

theorem toMat_eq_of_eqM {d : ℕ} {X Y : Array V} (h : eqM d X Y = true) : toMat d X = toMat d Y := by
  unfold eqM at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at h
  ext i j
  rw [toMat_apply, toMat_apply]
  exact V.val_ext (h.2 i (List.mem_finRange _)) j.val

theorem wsChar_eq_asciiWhitespace : wsChar = CFSG.Blueprint.NativeSporadic.asciiWhitespace := by
  funext c; unfold wsChar; rfl

theorem decode_apply_eq_decodeEntries (d : ℕ) (s : String) (i j : Fin d) :
    CFSG.Blueprint.NativeSporadic.decode 3 d 1 s i j =
      (((decodeEntries s)[i.val * d + j.val]?.getD 0 : ℕ) : ZMod 3) := by
  unfold decodeEntries
  rw [wsChar_eq_asciiWhitespace]
  rfl

theorem toMat_rowsOf (d : ℕ) (s : String) :
    toMat d (rowsOf d s) = CFSG.Blueprint.NativeSporadic.decode 3 d 1 s := by
  ext i j
  rw [decode_apply_eq_decodeEntries, toMat_apply]
  unfold rowsOf
  rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn, V.val_ofFn, ite_eq_left j.isLt,
    List.getElem?_toArray]

theorem RowsWF.rowsOf (d : ℕ) (s : String) : RowsWF (rowsOf d s) := by
  intro j
  unfold Native.rowsOf
  by_cases hj : j < d
  · rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
    exact V.wf_ofFn _ _
  · rw [getElem!_neg _ j (by simpa using hj)]; exact V.wf_zero

end CFSG.F3.Native
