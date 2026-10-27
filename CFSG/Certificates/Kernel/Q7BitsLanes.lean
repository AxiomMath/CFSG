module

public import Certificates.Data.Kernel.Q7Bits.Defs
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastA
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7FastB
public import CFSG.ClassicalInvolution.Phan.PhanS21Q7Sound

public section

namespace CFSG.Certificates.Kernel.Q7Bits.Lanes

open CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

private theorem force_eq {β : Sort _} (y : Nat) (k : Nat → β) : forceN y k = k y := by
  unfold forceN
  cases h : Nat.beq y 0
  · rfl
  · rw [Nat.eq_of_beq_eq_true h]
    rfl

private def bt (x L : Nat) : Bool := x.testBit (L + 64)

private theorem bt_xor (a b L : Nat) : bt (Nat.xor a b) L = (bt a L ^^ bt b L) :=
  Nat.testBit_xor a b (L + 64)

private theorem bt_land (a b L : Nat) : bt (Nat.land a b) L = (bt a L && bt b L) :=
  Nat.testBit_and a b (L + 64)

private theorem bt_lor (a b L : Nat) : bt (Nat.lor a b) L = (bt a L || bt b L) :=
  Nat.testBit_or a b (L + 64)

private theorem mix_lt (i : Nat) : mix i < 2 ^ 64 := by
  unfold mix
  exact Nat.mod_lt _ (by norm_num)

private theorem bt_mix (i L : Nat) : bt (mix i) L = false :=
  Nat.testBit_lt_two_pow
    (lt_of_lt_of_le (mix_lt i) (Nat.pow_le_pow_right (by norm_num) (by omega)))

private theorem bt_zero (L : Nat) : bt 0 L = false := Nat.zero_testBit _

private theorem bt_MM {L : Nat} (hL : L < NL) : bt MM L = true := by
  unfold bt MM
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (by omega)

private theorem bt_two_pow (r L : Nat) : bt (2 ^ (r + 64)) L = decide (r = L) := by
  unfold bt
  rw [Nat.testBit_two_pow]
  exact decide_eq_decide.2 (by omega)

private theorem bt_shift (p s L : Nat) :
    bt ((p >>> 64) <<< (s + 64)) L = (decide (s ≤ L) && bt p (L - s)) := by
  unfold bt
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s ≤ L
  · rw [show L + 64 - (s + 64) = L - s by omega, Nat.add_comm 64 (L - s)]
    simp [h]
  · simp [h]

private theorem bt_xor_mix (a i L : Nat) : bt (Nat.xor a (mix i)) L = bt a L := by
  rw [bt_xor, bt_mix, Bool.xor_false]

private def v3 (a b c : Bool) : ZMod 7 := ((a.toNat + 2 * b.toNat + 4 * c.toNat : Nat) : ZMod 7)

private def nv (x : P3) (L : Nat) : Nat :=
  (bt x.b0 L).toNat + 2 * (bt x.b1 L).toNat + 4 * (bt x.b2 L).toNat

private def lv (x : P3) (L : Nat) : ZMod 7 := v3 (bt x.b0 L) (bt x.b1 L) (bt x.b2 L)

private theorem lv_eq_nv (x : P3) (L : Nat) : lv x L = (nv x L : ZMod 7) := rfl

private theorem v3_testBit (n : Nat) :
    v3 (n.testBit 0) (n.testBit 1) (n.testBit 2) = ((n % 8 : Nat) : ZMod 7) := by
  unfold v3
  rw [Nat.toNat_testBit, Nat.toNat_testBit, Nat.toNat_testBit]
  congr 1
  simp only [pow_zero, pow_one, Nat.div_one, show (2 : Nat) ^ 2 = 4 by norm_num]
  omega

private theorem v3_fff : v3 false false false = 0 := by decide

private theorem lv_z3 (L : Nat) : lv z3 L = 0 := by
  simp only [lv, z3, bt_zero, v3_fff]

private def ladd (x y : P3) : P3 := laddK x y id

private theorem laddK_eq {β : Sort _} (x y : P3) (k : P3 → β) : laddK x y k = k (ladd x y) := by
  simp only [ladd, laddK, force_eq, id]

private theorem lv_ladd (x y : P3) (L : Nat) : lv (ladd x y) L = lv x L + lv y L := by
  simp only [ladd, laddK, force_eq, id, lv, bt_xor, bt_land, bt_lor]
  generalize bt x.b0 L = a0
  generalize bt x.b1 L = a1
  generalize bt x.b2 L = a2
  generalize bt y.b0 L = b0
  generalize bt y.b1 L = b1
  generalize bt y.b2 L = b2
  cases a0 <;> cases a1 <;> cases a2 <;> cases b0 <;> cases b1 <;> cases b2 <;> decide

private theorem bt_ladd_zero {x y : P3} {L : Nat} (hx0 : bt x.b0 L = false)
    (hx1 : bt x.b1 L = false) (hx2 : bt x.b2 L = false) (hy0 : bt y.b0 L = false)
    (hy1 : bt y.b1 L = false) (hy2 : bt y.b2 L = false) :
    bt (ladd x y).b0 L = false ∧ bt (ladd x y).b1 L = false ∧ bt (ladd x y).b2 L = false := by
  simp only [ladd, laddK, force_eq, id, bt_xor, bt_land, bt_lor, hx0, hx1, hx2, hy0, hy1, hy2]
  decide

private def sumA : P3 → List P3 → P3
  | a, [] => a
  | a, x :: l => sumA (ladd a x) l

private theorem sumAK_eq {β : Sort _} (a : P3) (l : List P3) (k : P3 → β) :
    sumAK a l k = k (sumA a l) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [sumAK, laddK_eq, ih, sumA]

private theorem lv_sumA (a : P3) (l : List P3) (L : Nat) :
    lv (sumA a l) L = lv a L + (l.map (lv · L)).sum := by
  induction l generalizing a with
  | nil => simp [sumA]
  | cons x l ih => simp only [sumA, ih, lv_ladd, List.map_cons, List.sum_cons, add_assoc]

private def sumP : List P3 → P3
  | [] => z3
  | x :: l => sumA x l

private theorem sumK_eq {β : Sort _} (l : List P3) (k : P3 → β) : sumK l k = k (sumP l) := by
  cases l <;> simp only [sumK, sumP, sumAK_eq]

private theorem lv_sumP (l : List P3) (L : Nat) : lv (sumP l) L = (l.map (lv · L)).sum := by
  cases l with
  | nil => simp [sumP, lv_z3]
  | cons x l => simp [sumP, lv_sumA]

private def orP : Option Nat → Bool → Nat → Option Nat
  | none, b, q => bif b then some q else none
  | some a, b, q => bif b then some (Nat.lor a q) else some a

private theorem orO_eq {β : Sort _} (a : Option Nat) (b : Bool) (q : Nat) (k : Option Nat → β) :
    orO a b q k = k (orP a b q) := by
  cases a <;> cases b <;> simp only [orO, orP, cond_true, cond_false, force_eq]

private theorem bt_orP (a : Option Nat) (b : Bool) (q L : Nat) :
    bt ((orP a b q).getD 0) L = (bt (a.getD 0) L || (b && bt q L)) := by
  cases a <;> cases b <;>
    simp only [orP, cond_true, cond_false, Option.getD_some, Option.getD_none, bt_lor, bt_zero,
      Bool.false_or, Bool.true_and, Bool.false_and, Bool.or_false]

private def selP (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 : Nat) : Nat :=
  (orP (orP (orP (orP (orP (orP (orP (orP none ((t 0).testBit j) q0) ((t 1).testBit j) q1)
    ((t 2).testBit j) q2) ((t 3).testBit j) q3) ((t 4).testBit j) q4) ((t 5).testBit j) q5)
    ((t 6).testBit j) q6) ((t 0).testBit j) q7).getD 0

private theorem selK_eq {β : Sort _} (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 : Nat)
    (k : Nat → β) : selK t j q0 q1 q2 q3 q4 q5 q6 q7 k = k (selP t j q0 q1 q2 q3 q4 q5 q6 q7) := by
  simp only [selK, orO_eq, selP]

private theorem bt_selP (t : Nat → Nat) (j q0 q1 q2 q3 q4 q5 q6 q7 L : Nat) :
    bt (selP t j q0 q1 q2 q3 q4 q5 q6 q7) L =
      ((t 0).testBit j && bt q0 L || (t 1).testBit j && bt q1 L || (t 2).testBit j && bt q2 L ||
        (t 3).testBit j && bt q3 L || (t 4).testBit j && bt q4 L || (t 5).testBit j && bt q5 L ||
        (t 6).testBit j && bt q6 L || (t 0).testBit j && bt q7 L) := by
  simp only [selP, bt_orP, Option.getD_none, bt_zero, Bool.false_or]

private def lmap (m : Nat) (x : P3) (t : Nat → Nat) : P3 := lmapK m x t id

private theorem lmapK_eq {β : Sort _} (m : Nat) (x : P3) (t : Nat → Nat) (k : P3 → β) :
    lmapK m x t k = k (lmap m x t) := by
  simp only [lmap, lmapK, force_eq, selK_eq, id]

private theorem lv_lmap {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) (t : Nat → Nat) :
    lv (lmap m x t) L = ((t (nv x L % 7) % 8 : Nat) : ZMod 7) := by
  rw [← v3_testBit]
  simp only [lmap, lmapK, force_eq, selK_eq, id, lv, nv, bt_selP, bt_land, bt_xor, hm]
  generalize bt x.b0 L = a0
  generalize bt x.b1 L = a1
  generalize bt x.b2 L = a2
  cases a0 <;> cases a1 <;> cases a2 <;> simp

private theorem lv_lmap_mul {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) (j : Nat) :
    lv (lmap m x (fun v => j * v % 7)) L = (j : ZMod 7) * lv x L := by
  rw [lv_lmap hm, Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (show 7 > 0 by norm_num)) (show 7 ≤ 8 by norm_num)),
    lv_eq_nv, natCast_mod_seven, Nat.cast_mul, natCast_mod_seven]

private theorem cast_seven_sub {q : Nat} (hq : q ≤ 7) :
    (((7 - q) % 7 : Nat) : ZMod 7) = -(q : ZMod 7) := by
  rw [natCast_mod_seven, Nat.cast_sub hq, Nat.cast_ofNat, seven_eq_zero, zero_sub]

private theorem lv_lmap_nsq {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) :
    lv (lmap m x (fun v => (7 - v * v % 7) % 7)) L = -(lv x L ^ 2) := by
  rw [lv_lmap hm, Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (show 7 > 0 by norm_num)) (show 7 ≤ 8 by norm_num)),
    cast_seven_sub (Nat.mod_lt _ (show 7 > 0 by norm_num)).le, natCast_mod_seven,
    Nat.cast_mul, natCast_mod_seven, lv_eq_nv, sq]

private theorem lv_lmap_sqs {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) (s : Nat) :
    lv (lmap m x (fun v => s * (v * v) % 7)) L = (s : ZMod 7) * lv x L ^ 2 := by
  rw [lv_lmap hm, Nat.mod_eq_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (show 7 > 0 by norm_num)) (show 7 ≤ 8 by norm_num)),
    natCast_mod_seven, Nat.cast_mul, Nat.cast_mul, natCast_mod_seven, lv_eq_nv, sq]

private theorem lzero_bits (a0 a1 a2 : Bool) :
    ((a0 ^^ a1 || a1 ^^ a2) ^^ true) = decide (v3 a0 a1 a2 = 0) := by
  cases a0 <;> cases a1 <;> cases a2 <;> decide

private theorem bt_lzero {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) :
    bt (lzero m x) L = decide (lv x L = 0) := by
  simp only [lzero, bt_xor, bt_lor, hm, lv]
  exact lzero_bits _ _ _

private theorem bt_nz {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) :
    bt (Nat.xor (lzero m x) m) L = !decide (lv x L = 0) := by
  rw [bt_xor, bt_lzero hm, hm, Bool.xor_true]

private def tblA (m : Nat) (x : P3) : List Nat → List P3
  | [] => []
  | j :: js => lmap m x (fun v => j * v % 7) :: tblA m x js

private theorem tblAK_eq {β : Sort _} (m : Nat) (x : P3) (js : List Nat) (k : List P3 → β) :
    tblAK m x js k = k (tblA m x js) := by
  induction js generalizing k with
  | nil => rfl
  | cons j js ih => simp only [tblAK, lmapK_eq, ih, tblA]

private def tbl (m : Nat) (x : P3) : List P3 := z3 :: x :: tblA m x [2, 3, 4, 5, 6]

private theorem tblK_eq {β : Sort _} (m : Nat) (x : P3) (k : List P3 → β) :
    tblK m x k = k (tbl m x) := by
  simp only [tblK, tblAK_eq, tbl]

private def tbP (m : Nat) (x : P6) : Tb := ⟨tbl m x.re, tbl m x.im⟩

private theorem tbPK_eq {β : Sort _} (m : Nat) (x : P6) (k : Tb → β) :
    tbPK m x k = k (tbP m x) := by
  simp only [tbPK, tblK_eq, tbP]

private def Tok (t : List P3) (L : Nat) : Prop :=
  ∀ i < 7, lv (sel t i) L = (i : ZMod 7) * lv (sel t 1) L

private theorem sel_tbl_one (m : Nat) (x : P3) : sel (tbl m x) 1 = x := rfl

private theorem tbl_eq (m : Nat) (x : P3) :
    tbl m x = [z3, x, lmap m x (fun v => 2 * v % 7), lmap m x (fun v => 3 * v % 7),
      lmap m x (fun v => 4 * v % 7), lmap m x (fun v => 5 * v % 7),
      lmap m x (fun v => 6 * v % 7)] := by
  simp only [tbl, tblA]

private theorem sel7 (y0 y1 y2 y3 y4 y5 y6 : P3) :
    sel [y0, y1, y2, y3, y4, y5, y6] 0 = y0 ∧ sel [y0, y1, y2, y3, y4, y5, y6] 1 = y1 ∧
      sel [y0, y1, y2, y3, y4, y5, y6] 2 = y2 ∧ sel [y0, y1, y2, y3, y4, y5, y6] 3 = y3 ∧
      sel [y0, y1, y2, y3, y4, y5, y6] 4 = y4 ∧ sel [y0, y1, y2, y3, y4, y5, y6] 5 = y5 ∧
      sel [y0, y1, y2, y3, y4, y5, y6] 6 = y6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem tbl_ok {m : Nat} {x : P3} {L : Nat} (hm : bt m L = true) : Tok (tbl m x) L := by
  intro i hi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := sel7 z3 x (lmap m x (fun v => 2 * v % 7))
    (lmap m x (fun v => 3 * v % 7)) (lmap m x (fun v => 4 * v % 7))
    (lmap m x (fun v => 5 * v % 7)) (lmap m x (fun v => 6 * v % 7))
  rw [tbl_eq, h1]
  interval_cases i
  · rw [h0, lv_z3, Nat.cast_zero, zero_mul]
  · rw [h1, Nat.cast_one, one_mul]
  · rw [h2]; exact lv_lmap_mul hm 2
  · rw [h3]; exact lv_lmap_mul hm 3
  · rw [h4]; exact lv_lmap_mul hm 4
  · rw [h5]; exact lv_lmap_mul hm 5
  · rw [h6]; exact lv_lmap_mul hm 6

private def TbOk (t : Tb) (L : Nat) : Prop := Tok t.r L ∧ Tok t.i L

private def tv (t : Tb) (L : Nat) : GF49 := ⟨lv (sel t.r 1) L, lv (sel t.i 1) L⟩

private def lv6 (x : P6) (L : Nat) : GF49 := ⟨lv x.re L, lv x.im L⟩

private theorem tbP_ok {m : Nat} {x : P6} {L : Nat} (hm : bt m L = true) : TbOk (tbP m x) L :=
  ⟨tbl_ok hm, tbl_ok hm⟩

private theorem tv_tbP (m : Nat) (x : P6) (L : Nat) : tv (tbP m x) L = lv6 x L := rfl

private def addP (a : Option P3) (l : List P3) (i : Nat) : Option P3 :=
  bif Nat.beq i 0 then a else
    match a with
    | none => some (sel l i)
    | some a => some (ladd a (sel l i))

private theorem addO_eq {β : Sort _} (a : Option P3) (l : List P3) (i : Nat)
    (k : Option P3 → β) : addO a l i k = k (addP a l i) := by
  unfold addO addP
  cases h : Nat.beq i 0 <;> cases a <;> simp only [cond_true, cond_false, laddK_eq]

private def lvo (o : Option P3) (L : Nat) : ZMod 7 := lv (o.getD z3) L

private theorem lvo_addP {a : Option P3} {l : List P3} {i L : Nat} (hl : Tok l L) (hi : i < 7) :
    lvo (addP a l i) L = lvo a L + (i : ZMod 7) * lv (sel l 1) L := by
  unfold addP
  cases i with
  | zero =>
    show lvo a L = lvo a L + ((0 : Nat) : ZMod 7) * lv (sel l 1) L
    rw [Nat.cast_zero, zero_mul, add_zero]
  | succ n =>
    rw [show Nat.beq (n + 1) 0 = false from rfl, cond_false, ← hl (n + 1) hi]
    cases a with
    | none => simp only [lvo, Option.getD_some, Option.getD_none, lv_z3, zero_add]
    | some a => simp only [lvo, Option.getD_some, lv_ladd]

private theorem sum_toList (o : Option P3) (L : Nat) :
    (o.toList.map (lv · L)).sum = lvo o L := by
  cases o <;> simp [lvo, lv_z3]

private def linA : Option P3 → Option P3 → List (Tb × Nat) → P6
  | r, i, [] => ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l =>
    linA (addP (addP r t.r (a % 7)) t.i ((7 - a / 7 % 7) % 7))
      (addP (addP i t.r (a / 7 % 7)) t.i (a % 7)) l

private theorem linAK_eq {β : Sort _} (r i : Option P3) (l : List (Tb × Nat)) (k : P6 → β) :
    linAK r i l k = k (linA r i l) := by
  induction l generalizing r i with
  | nil => rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    simp only [linAK, force_eq, addO_eq, ih, linA]

private theorem linK_eq {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) :
    linK l k = k (linA none none l) :=
  linAK_eq none none l k

private def linCA : Option P3 → Option P3 → List (Tb × Nat) → P6
  | r, i, [] => ⟨r.getD z3, i.getD z3⟩
  | r, i, (t, a) :: l =>
    linCA (addP (addP r t.r (a % 7)) t.i (a / 7 % 7))
      (addP (addP i t.r (a / 7 % 7)) t.i ((7 - a % 7) % 7)) l

private theorem linCAK_eq {β : Sort _} (r i : Option P3) (l : List (Tb × Nat)) (k : P6 → β) :
    linCAK r i l k = k (linCA r i l) := by
  induction l generalizing r i with
  | nil => rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    simp only [linCAK, force_eq, addO_eq, ih, linCA]

private theorem linCK_eq {β : Sort _} (l : List (Tb × Nat)) (k : P6 → β) :
    linCK l k = k (linCA none none l) :=
  linCAK_eq none none l k

private theorem lv6_linA {L : Nat} (r i : Option P3) (l : List (Tb × Nat))
    (hl : ∀ ta ∈ l, TbOk ta.1 L) :
    lv6 (linA r i l) L = ⟨lvo r L, lvo i L⟩ + (l.map fun ta => gfDec ta.2 * tv ta.1 L).sum := by
  induction l generalizing r i with
  | nil =>
    simp only [linA, List.map_nil, List.sum_nil, add_zero]
    rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    have ht : TbOk t L := hl (t, a) List.mem_cons_self
    rw [linA, ih _ _ (fun ta h => hl ta (List.mem_cons_of_mem _ h)),
      lvo_addP ht.2 (Nat.mod_lt _ (by norm_num)), lvo_addP ht.1 (Nat.mod_lt _ (by norm_num)),
      lvo_addP ht.2 (Nat.mod_lt _ (by norm_num)), lvo_addP ht.1 (Nat.mod_lt _ (by norm_num))]
    simp only [List.map_cons, List.sum_cons]
    rw [← add_assoc]
    congr 1
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, gfDec_re, gfDec_im, tv]
      rw [cast_seven_sub (Nat.mod_lt _ (by norm_num)).le, natCast_mod_seven, natCast_mod_seven]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, gfDec_re, gfDec_im, tv]
      rw [natCast_mod_seven, natCast_mod_seven]
      ring

private theorem lv6_linCA {L : Nat} (r i : Option P3) (l : List (Tb × Nat))
    (hl : ∀ ta ∈ l, TbOk ta.1 L) :
    lv6 (linCA r i l) L =
      ⟨lvo r L, lvo i L⟩ + (l.map fun ta => gfDec ta.2 * star (tv ta.1 L)).sum := by
  induction l generalizing r i with
  | nil =>
    simp only [linCA, List.map_nil, List.sum_nil, add_zero]
    rfl
  | cons ta l ih =>
    obtain ⟨t, a⟩ := ta
    have ht : TbOk t L := hl (t, a) List.mem_cons_self
    rw [linCA, ih _ _ (fun ta h => hl ta (List.mem_cons_of_mem _ h)),
      lvo_addP ht.2 (Nat.mod_lt _ (by norm_num)), lvo_addP ht.1 (Nat.mod_lt _ (by norm_num)),
      lvo_addP ht.2 (Nat.mod_lt _ (by norm_num)), lvo_addP ht.1 (Nat.mod_lt _ (by norm_num))]
    simp only [List.map_cons, List.sum_cons]
    rw [← add_assoc]
    congr 1
    apply QuadraticAlgebra.ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star,
        QuadraticAlgebra.im_star, gfDec_re, gfDec_im, tv]
      rw [natCast_mod_seven, natCast_mod_seven]
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
        QuadraticAlgebra.im_star, gfDec_re, gfDec_im, tv]
      rw [cast_seven_sub (Nat.mod_lt _ (by norm_num)).le, natCast_mod_seven, natCast_mod_seven]
      ring

private def nsq (m : Nat) (x : P6) : List P3 :=
  [lmap m x.re (fun v => (7 - v * v % 7) % 7), lmap m x.im (fun v => (7 - v * v % 7) % 7)]

private theorem nsqK_eq {β : Sort _} (m : Nat) (x : P6) (k : List P3 → β) :
    nsqK m x k = k (nsq m x) := by
  simp only [nsqK, lmapK_eq, nsq]

private def nrm (z : GF49) : ZMod 7 := z.re ^ 2 + z.im ^ 2

private theorem sum_nsq {m : Nat} {x : P6} {L : Nat} (hm : bt m L = true) :
    ((nsq m x).map (lv · L)).sum = -nrm (lv6 x L) := by
  simp only [nsq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lv_lmap_nsq hm, nrm,
    lv6]
  ring

private def sqs (m s : Nat) (x : P6) : List P3 :=
  [lmap m x.re (fun v => s * (v * v) % 7), lmap m x.im (fun v => s * (v * v) % 7)]

private theorem sqsK_eq {β : Sort _} (m s : Nat) (x : P6) (k : List P3 → β) :
    sqsK m s x k = k (sqs m s x) := by
  simp only [sqsK, lmapK_eq, sqs]

private theorem sum_sqs {m : Nat} {x : P6} {L : Nat} (hm : bt m L = true) (s : Nat) :
    ((sqs m s x).map (lv · L)).sum = (s : ZMod 7) * nrm (lv6 x L) := by
  simp only [sqs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lv_lmap_sqs hm, nrm,
    lv6]
  ring

private def herUU (m : Nat) (u0 u1 u2 u4 u5 u6 : P6) : P3 :=
  sumP (sqs m 1 u0 ++ sqs m 1 u1 ++ sqs m 1 u2 ++ sqs m 1 u4 ++ sqs m 1 u5 ++ sqs m gfKappa u6)

private theorem herUUK_eq {β : Sort _} (m : Nat) (u0 u1 u2 u4 u5 u6 : P6) (k : P3 → β) :
    herUUK m u0 u1 u2 u4 u5 u6 k = k (herUU m u0 u1 u2 u4 u5 u6) := by
  simp only [herUUK, sqsK_eq, sumK_eq, herUU]

private theorem lv_herUU {m L : Nat} (hm : bt m L = true) (u0 u1 u2 u4 u5 u6 : P6) :
    lv (herUU m u0 u1 u2 u4 u5 u6) L = nrm (lv6 u0 L) + nrm (lv6 u1 L) + nrm (lv6 u2 L) +
      nrm (lv6 u4 L) + nrm (lv6 u5 L) + 5 * nrm (lv6 u6 L) := by
  simp only [herUU, lv_sumP, List.map_append, List.sum_append, sum_sqs hm]
  simp only [gfKappa]
  push_cast
  ring

private def vtxM (m : Nat) (T : Tabs) (u0 : P6) (h : P3) (c : N7) : Nat :=
  Nat.land (Nat.land (Nat.xor (lzero m h) m) (Nat.xor (lzero m (sumP (h :: nsq m u0))) m))
    (Nat.xor (lzero m (sumP ((addP none T.th (herN c c % 7)).toList ++
      nsq m (linCA none none (hcCoef T c))))) m)

private theorem vtxMK_eq {β : Sort _} (m : Nat) (T : Tabs) (u0 : P6) (h : P3) (c : N7)
    (k : Nat → β) : vtxMK m T u0 h c k = k (vtxM m T u0 h c) := by
  simp only [vtxMK, nsqK_eq, sumK_eq, linCK_eq, force_eq, addO_eq, vtxM]

private def adjM (m : Nat) (T : Tabs) (v : N7) : Nat :=
  Nat.land (Nat.xor (lzero m (sumP ((addP none T.th (herN v v % 7)).toList ++
      nsq m (linA none none (herCoef T v))))) m)
    (Nat.land (lzero m (linA none none (bfCoef T v)).re) (lzero m (linA none none (bfCoef T v)).im))

private theorem adjMK_eq {β : Sort _} (m : Nat) (T : Tabs) (v : N7) (k : Nat → β) :
    adjMK m T v k = k (adjM m T v) := by
  simp only [adjMK, linK_eq, force_eq, nsqK_eq, addO_eq, sumK_eq, adjM]

private theorem laneVecK_eq {β : Sort _} (c : N7) (L : Nat) (k : N7 → β) :
    laneVecK c L k = k (laneVec c L) := by
  simp only [laneVecK, forceV7, force_eq]
  rfl

private theorem stepL_cons (m : Nat) (T : Tabs) (V S : Nat) (c : N7) (L : Nat) (Ls : List Nat)
    (a : Nat) : stepL m T V S c (L :: Ls) a = bif S.testBit (L + 64) && decide (L < NL) then
      stepL m T V S c Ls (Nat.xor (Nat.lor a (Nat.land V (adjM m T (laneVec c L)))) (mix L))
    else none := by
  simp only [stepL, laneVecK_eq, adjMK_eq, force_eq]

private abbrev B6 := Bool × Bool × Bool × Bool × Bool × Bool

private def bits6 (x : P6) (L : Nat) : B6 :=
  (bt x.re.b0 L, bt x.re.b1 L, bt x.re.b2 L, bt x.im.b0 L, bt x.im.b1 L, bt x.im.b2 L)

private def val6 (t : B6) : GF49 :=
  ⟨v3 t.1 t.2.1 t.2.2.1, v3 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2⟩

private theorem lv6_eq (x : P6) (L : Nat) : lv6 x L = val6 (bits6 x L) := rfl

private def z6b : B6 := (false, false, false, false, false, false)

private theorem val6_z6b : val6 z6b = 0 := by
  ext <;> simp only [val6, z6b, v3_fff, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]

private def dg6 (a : Nat) : B6 :=
  ((a % 7).testBit 0, (a % 7).testBit 1, (a % 7).testBit 2, (a / 7).testBit 0,
    (a / 7).testBit 1, (a / 7).testBit 2)

private theorem val6_dg6 {a : Nat} (ha : a < 49) : val6 (dg6 a) = gfDec a := by
  have h1 : a % 7 % 8 = a % 7 := Nat.mod_eq_of_lt (by omega)
  have h2 : a / 7 % 8 = a / 7 := Nat.mod_eq_of_lt (by omega)
  simp only [val6, dg6, v3_testBit, h1, h2]
  rfl

private def LZp (p w : Nat) : Prop := ∀ L, w ≤ L → bt p L = false

private def LZ6 (x : P6) (w : Nat) : Prop :=
  LZp x.re.b0 w ∧ LZp x.re.b1 w ∧ LZp x.re.b2 w ∧ LZp x.im.b0 w ∧ LZp x.im.b1 w ∧ LZp x.im.b2 w

private theorem bits6_of_lz6 {x : P6} {w L : Nat} (h : LZ6 x w) (hL : w ≤ L) :
    bits6 x L = z6b := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [bits6, z6b, h0 L hL, h1 L hL, h2 L hL, h3 L hL, h4 L hL, h5 L hL]

private theorem lv6_of_lz6 {x : P6} {w L : Nat} (h : LZ6 x w) (hL : w ≤ L) : lv6 x L = 0 := by
  rw [lv6_eq, bits6_of_lz6 h hL, val6_z6b]

private theorem bits6_z6 (L : Nat) : bits6 z6 L = z6b := by
  simp only [bits6, z6, z3, bt_zero, z6b]

private theorem lv6_z6 (L : Nat) : lv6 z6 L = 0 := by
  rw [lv6_eq, bits6_z6, val6_z6b]

private theorem lz6_z6 (w : Nat) : LZ6 z6 w :=
  ⟨fun L _ => bt_zero L, fun L _ => bt_zero L, fun L _ => bt_zero L, fun L _ => bt_zero L,
    fun L _ => bt_zero L, fun L _ => bt_zero L⟩

private theorem bt_constB (v j n s L : Nat) :
    bt (constB v j n s) L = (v.testBit j && decide (L < n)) := by
  rw [constB, bt_xor_mix]
  cases v.testBit j
  · rw [cond_false, bt_zero, Bool.false_and]
  · rw [cond_true, Bool.true_and]
    unfold bt
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
      decide_eq_true (show L + 64 ≥ 64 by omega), Bool.true_and, Nat.add_sub_cancel]

private theorem bits6_constP (a n s L : Nat) :
    bits6 (constP a n s) L = bif decide (L < n) then dg6 a else z6b := by
  simp only [bits6, constP, bt_constB, dg6, z6b]
  cases decide (L < n) <;> simp only [Bool.and_false, Bool.and_true, cond_false, cond_true]

private theorem lv6_constP {a n s L : Nat} (ha : a < 49) (hL : L < n) :
    lv6 (constP a n s) L = gfDec a := by
  rw [lv6_eq, bits6_constP, decide_eq_true hL, cond_true, val6_dg6 ha]

private theorem lz6_constP (a n s : Nat) : LZ6 (constP a n s) n := by
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
    fun L hL => ?_⟩ <;>
    simp only [constP, bt_constB, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]

private def tabS (f : Nat → Nat) (i : Nat) (acc : P6) : P6 :=
  ⟨⟨Nat.xor (Nat.lor acc.re.b0 (bif (f i % 7).testBit 0 then 2 ^ (i + 64) else 0)) (mix (6 * i)),
      Nat.xor (Nat.lor acc.re.b1 (bif (f i % 7).testBit 1 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 1)),
      Nat.xor (Nat.lor acc.re.b2 (bif (f i % 7).testBit 2 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 2))⟩,
    ⟨Nat.xor (Nat.lor acc.im.b0 (bif (f i / 7).testBit 0 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 3)),
      Nat.xor (Nat.lor acc.im.b1 (bif (f i / 7).testBit 1 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 4)),
      Nat.xor (Nat.lor acc.im.b2 (bif (f i / 7).testBit 2 then 2 ^ (i + 64) else 0))
        (mix (6 * i + 5))⟩⟩

private def tab (f : Nat → Nat) : Nat → Nat → P6 → P6
  | _, 0, acc => acc
  | i, n + 1, acc => tab f (i + 1) n (tabS f i acc)

private theorem tabK_eq {β : Sort _} (f : Nat → Nat) (i n : Nat) (acc : P6) (k : P6 → β) :
    tabK f i n acc k = k (tab f i n acc) := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih => simp only [tabK, force_eq, ih, tab, tabS]

private theorem bt_bif (b : Bool) (i L : Nat) :
    bt (bif b then 2 ^ (i + 64) else 0) L = (b && decide (i = L)) := by
  cases b
  · rw [cond_false, bt_zero, Bool.false_and]
  · rw [cond_true, bt_two_pow, Bool.true_and]

private theorem bt_tab_gen (f : Nat → Nat) (pr : P6 → Nat) (dg : Nat → Bool) (L : Nat)
    (hstep : ∀ i acc, bt (pr (tabS f i acc)) L = (bt (pr acc) L || (dg i && decide (i = L)))) :
    ∀ n i acc, bt (pr (tab f i n acc)) L =
      (bt (pr acc) L || (dg L && decide (i ≤ L ∧ L < i + n)))
  | 0, i, acc => by
    rw [tab, decide_eq_false (show ¬(i ≤ L ∧ L < i + 0) by omega), Bool.and_false, Bool.or_false]
  | n + 1, i, acc => by
    rw [tab, bt_tab_gen f pr dg L hstep n (i + 1) (tabS f i acc), hstep]
    by_cases h : i = L
    · rw [decide_eq_true h, decide_eq_false (show ¬(i + 1 ≤ L ∧ L < i + 1 + n) by omega),
        decide_eq_true (show i ≤ L ∧ L < i + (n + 1) by omega), h, Bool.and_true, Bool.and_false,
        Bool.or_false]
    · rw [decide_eq_false h, Bool.and_false, Bool.or_false,
        decide_eq_decide.2 (show i + 1 ≤ L ∧ L < i + 1 + n ↔ i ≤ L ∧ L < i + (n + 1) by omega)]

private theorem bt_tab0 (f : Nat → Nat) (pr : P6 → Nat) (dg : Nat → Bool) (L n : Nat)
    (hstep : ∀ i acc, bt (pr (tabS f i acc)) L = (bt (pr acc) L || (dg i && decide (i = L))))
    (hz : bt (pr z6) L = false) :
    bt (pr (tab f 0 n z6)) L = (dg L && decide (L < n)) := by
  rw [bt_tab_gen f pr dg L hstep n 0 z6, hz, Bool.false_or,
    decide_eq_decide.2 (show 0 ≤ L ∧ L < 0 + n ↔ L < n by omega)]

private theorem bt6_tab (f : Nat → Nat) (n L : Nat) :
    bt (tab f 0 n z6).re.b0 L = ((f L % 7).testBit 0 && decide (L < n)) ∧
    bt (tab f 0 n z6).re.b1 L = ((f L % 7).testBit 1 && decide (L < n)) ∧
    bt (tab f 0 n z6).re.b2 L = ((f L % 7).testBit 2 && decide (L < n)) ∧
    bt (tab f 0 n z6).im.b0 L = ((f L / 7).testBit 0 && decide (L < n)) ∧
    bt (tab f 0 n z6).im.b1 L = ((f L / 7).testBit 1 && decide (L < n)) ∧
    bt (tab f 0 n z6).im.b2 L = ((f L / 7).testBit 2 && decide (L < n)) :=
  ⟨bt_tab0 f (fun x => x.re.b0) (fun i => (f i % 7).testBit 0) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L),
    bt_tab0 f (fun x => x.re.b1) (fun i => (f i % 7).testBit 1) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L),
    bt_tab0 f (fun x => x.re.b2) (fun i => (f i % 7).testBit 2) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L),
    bt_tab0 f (fun x => x.im.b0) (fun i => (f i / 7).testBit 0) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L),
    bt_tab0 f (fun x => x.im.b1) (fun i => (f i / 7).testBit 1) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L),
    bt_tab0 f (fun x => x.im.b2) (fun i => (f i / 7).testBit 2) L n
      (fun i acc => by simp only [tabS, bt_xor_mix, bt_lor, bt_bif]) (bt_zero L)⟩

private theorem bits6_tab (f : Nat → Nat) (n L : Nat) :
    bits6 (tab f 0 n z6) L = bif decide (L < n) then dg6 (f L) else z6b := by
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := bt6_tab f n L
  rw [bits6, e0, e1, e2, e3, e4, e5]
  cases decide (L < n) <;> simp only [Bool.and_false, Bool.and_true, cond_false, cond_true, dg6, z6b]

private theorem lz6_tab (f : Nat → Nat) (n : Nat) : LZ6 (tab f 0 n z6) n := by
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
    fun L hL => ?_⟩
  · rw [(bt6_tab f n L).1, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]
  · rw [(bt6_tab f n L).2.1, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]
  · rw [(bt6_tab f n L).2.2.1, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]
  · rw [(bt6_tab f n L).2.2.2.1, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]
  · rw [(bt6_tab f n L).2.2.2.2.1, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]
  · rw [(bt6_tab f n L).2.2.2.2.2, decide_eq_false (Nat.not_lt.2 hL), Bool.and_false]

private theorem lv6_tab {f : Nat → Nat} {n L : Nat} (hL : L < n) (hf : f L < 49) :
    lv6 (tab f 0 n z6) L = gfDec (f L) := by
  rw [lv6_eq, bits6_tab, decide_eq_true hL, cond_true, val6_dg6 hf]

private theorem bt_rep {p w : Nat} (hp : LZp p w) (L : Nat) :
    ∀ n, bt (rep p w n) L = (decide (L < w * n) && bt p (L % w))
  | 0 => by
    rw [rep, bt_zero, Nat.mul_zero, decide_eq_false (Nat.not_lt_zero L), Bool.false_and]
  | n + 1 => by
    rw [rep, bt_xor_mix, bt_lor, bt_rep hp L n, bt_shift, Nat.mul_succ]
    by_cases h1 : L < w * n
    · rw [decide_eq_true h1, decide_eq_false (show ¬(w * n ≤ L) by omega),
        decide_eq_true (show L < w * n + w by omega)]
      simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    · by_cases h3 : L < w * n + w
      · have hmod : L % w = L - w * n := by
          have e : L = (L - w * n) + w * n := by omega
          conv_lhs => rw [e]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show L - w * n < w by omega)]
        rw [decide_eq_false h1, decide_eq_true (show w * n ≤ L by omega), decide_eq_true h3, hmod]
        simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
      · rw [decide_eq_false h1, decide_eq_true (show w * n ≤ L by omega), decide_eq_false h3,
          hp (L - w * n) (show w ≤ L - w * n by omega)]
        simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]

private theorem lzp_rep {p w : Nat} (hp : LZp p w) (n : Nat) : LZp (rep p w n) (w * n) :=
  fun L hL => by rw [bt_rep hp L n, decide_eq_false (Nat.not_lt.2 hL), Bool.false_and]

private theorem bt_ones (w s L : Nat) :
    bt ((2 ^ w - 1) <<< (s + 64)) L = decide (s ≤ L ∧ L < s + w) := by
  unfold bt
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, ← Bool.decide_and]
  exact decide_eq_decide.2 (by omega)

private theorem bt_spread (p w L : Nat) :
    ∀ n, bt (spread p w n) L = (decide (L < w * n) && bt p (L / w))
  | 0 => by
    rw [spread, bt_zero, Nat.mul_zero, decide_eq_false (Nat.not_lt_zero L), Bool.false_and]
  | n + 1 => by
    rw [spread, bt_xor_mix, bt_lor, bt_spread p w L n, Nat.mul_succ]
    have hb : bt (bif p.testBit (n + 64) then (2 ^ w - 1) <<< (w * n + 64) else 0) L =
        (bt p n && decide (w * n ≤ L ∧ L < w * n + w)) := by
      unfold bt
      cases p.testBit (n + 64)
      · rw [cond_false, Nat.zero_testBit, Bool.false_and]
      · rw [cond_true, Bool.true_and]
        exact bt_ones w (w * n) L
    rw [hb]
    by_cases h1 : L < w * n
    · rw [decide_eq_true h1, decide_eq_false (show ¬(w * n ≤ L ∧ L < w * n + w) by omega),
        decide_eq_true (show L < w * n + w by omega)]
      simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
    · by_cases h3 : L < w * n + w
      · have hw : 0 < w := by omega
        have e1 : n * w ≤ L := by rw [Nat.mul_comm]; omega
        have e2 : L < (n + 1) * w := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
        have e3 : n ≤ L / w := (Nat.le_div_iff_mul_le hw).2 e1
        have e4 : L / w < n + 1 := (Nat.div_lt_iff_lt_mul hw).2 e2
        have hdiv : L / w = n := by omega
        have hin : w * n ≤ L ∧ L < w * n + w := ⟨by omega, h3⟩
        rw [decide_eq_false h1, decide_eq_true hin, decide_eq_true h3, hdiv]
        simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
      · rw [decide_eq_false h1, decide_eq_false (show ¬(w * n ≤ L ∧ L < w * n + w) by omega),
          decide_eq_false h3]
        simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]

private theorem lzp_spread (p w n : Nat) : LZp (spread p w n) (w * n) :=
  fun L hL => by rw [bt_spread p w L n, decide_eq_false (Nat.not_lt.2 hL), Bool.false_and]

private theorem bits6_mapP (g : Nat → Nat) (s : Nat) (x : P6) (L : Nat) :
    bits6 (mapP g s x) L = (bt (g x.re.b0) L, bt (g x.re.b1) L, bt (g x.re.b2) L,
      bt (g x.im.b0) L, bt (g x.im.b1) L, bt (g x.im.b2) L) := by
  simp only [bits6, mapP, bt_xor_mix]

private theorem bits6_mapP_of {g : Nat → Nat} {s w : Nat} {x : P6} {L L' : Nat} {b : Bool}
    (hx : LZ6 x w) (hg : ∀ p, LZp p w → bt (g p) L = (b && bt p L')) :
    bits6 (mapP g s x) L = bif b then bits6 x L' else z6b := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hx
  rw [bits6_mapP, hg _ h0, hg _ h1, hg _ h2, hg _ h3, hg _ h4, hg _ h5]
  cases b <;> rfl

private theorem lz6_mapP {g : Nat → Nat} {s w W : Nat} {x : P6} (hx : LZ6 x w)
    (hg : ∀ p, LZp p w → LZp (g p) W) : LZ6 (mapP g s x) W := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hx
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
    fun L hL => ?_⟩ <;> simp only [mapP, bt_xor_mix]
  · exact hg _ h0 L hL
  · exact hg _ h1 L hL
  · exact hg _ h2 L hL
  · exact hg _ h3 L hL
  · exact hg _ h4 L hL
  · exact hg _ h5 L hL

private theorem lv6_spread {w n s v : Nat} {x : P6} {L : Nat} (hx : LZ6 x v) (hL : L < w * n) :
    lv6 (mapP (fun p => spread p w n) s x) L = lv6 x (L / w) := by
  rw [lv6_eq, bits6_mapP_of hx (fun p _ => bt_spread p w L n), decide_eq_true hL, cond_true]
  rfl

private theorem lz6_spread {w n s v W : Nat} {x : P6} (hx : LZ6 x v) (hW : w * n ≤ W) :
    LZ6 (mapP (fun p => spread p w n) s x) W :=
  lz6_mapP hx fun p _ L hL => lzp_spread p w n L (le_trans hW hL)

private theorem lv6_rep {w n s : Nat} {x : P6} {L : Nat} (hx : LZ6 x w) (hL : L < w * n) :
    lv6 (mapP (fun p => rep p w n) s x) L = lv6 x (L % w) := by
  rw [lv6_eq, bits6_mapP_of hx (fun p hp => bt_rep hp L n), decide_eq_true hL, cond_true]
  rfl

private theorem lz6_rep {w n s W : Nat} {x : P6} (hx : LZ6 x w) (hW : w * n ≤ W) :
    LZ6 (mapP (fun p => rep p w n) s x) W :=
  lz6_mapP hx fun _ hp L hL => lzp_rep hp n L (le_trans hW hL)

private theorem bt_rs (p L : Nat) : bt (rep (spread p 49 49) 2401 49) L =
    ((decide (L < 2401 * 49) && decide (L % 2401 < 49 * 49)) && bt p (L % 2401 / 49)) := by
  rw [bt_rep (p := spread p 49 49) (w := 2401) (lzp_spread p 49 49) L 49, bt_spread,
    Bool.and_assoc]

private theorem lv6_rs {s v : Nat} {x : P6} {L : Nat} (hx : LZ6 x v) (hL : L < 117649) :
    lv6 (mapP (fun p => rep (spread p 49 49) 2401 49) s x) L = lv6 x (L % 2401 / 49) := by
  rw [lv6_eq, bits6_mapP_of hx (fun p _ => bt_rs p L),
    decide_eq_true (show L < 2401 * 49 by omega),
    decide_eq_true (show L % 2401 < 49 * 49 by omega), Bool.true_and, cond_true]
  rfl

private theorem lz6_rs {s v : Nat} {x : P6} (hx : LZ6 x v) :
    LZ6 (mapP (fun p => rep (spread p 49 49) 2401 49) s x) 117649 :=
  lz6_mapP hx fun p _ L hL => by
    rw [bt_rs, decide_eq_false (show ¬(L < 2401 * 49) by omega), Bool.false_and, Bool.false_and]

private theorem bt_join1 {a b c : Nat} (d : Nat) (ha : LZp a 117649) (hb : LZp b 2401)
    (hc : LZp c 49) (L : Nat) :
    bt (join1 a b c d) L = if L < 117649 then bt a L else if L < 120050 then bt b (L - 117649)
      else if L < 120099 then bt c (L - 120050) else bt d (L - 120099) := by
  rw [join1, bt_lor, bt_lor, bt_lor, bt_shift, bt_shift, bt_shift]
  split_ifs with h1 h2 h3
  · rw [decide_eq_false (show ¬(117649 ≤ L) by omega), decide_eq_false (show ¬(120050 ≤ L) by omega),
      decide_eq_false (show ¬(120099 ≤ L) by omega)]
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
  · rw [ha L (show 117649 ≤ L by omega), decide_eq_true (show 117649 ≤ L by omega),
      decide_eq_false (show ¬(120050 ≤ L) by omega), decide_eq_false (show ¬(120099 ≤ L) by omega)]
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
  · rw [ha L (show 117649 ≤ L by omega), hb (L - 117649) (show 2401 ≤ L - 117649 by omega),
      decide_eq_true (show 117649 ≤ L by omega), decide_eq_true (show 120050 ≤ L by omega),
      decide_eq_false (show ¬(120099 ≤ L) by omega)]
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]
  · rw [ha L (show 117649 ≤ L by omega), hb (L - 117649) (show 2401 ≤ L - 117649 by omega),
      hc (L - 120050) (show 49 ≤ L - 120050 by omega), decide_eq_true (show 117649 ≤ L by omega),
      decide_eq_true (show 120050 ≤ L by omega), decide_eq_true (show 120099 ≤ L by omega)]
    simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or]

private theorem lv6_joinP {a b c d : P6} (ha : LZ6 a 117649) (hb : LZ6 b 2401) (hc : LZ6 c 49)
    (L : Nat) : lv6 (joinP a b c d) L = if L < 117649 then lv6 a L else if L < 120050 then
      lv6 b (L - 117649) else if L < 120099 then lv6 c (L - 120050) else lv6 d (L - 120099) := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb
  obtain ⟨c0, c1, c2, c3, c4, c5⟩ := hc
  simp only [lv6_eq, bits6, joinP, bt_join1 _ a0 b0 c0, bt_join1 _ a1 b1 c1,
    bt_join1 _ a2 b2 c2, bt_join1 _ a3 b3 c3, bt_join1 _ a4 b4 c4, bt_join1 _ a5 b5 c5]
  split_ifs <;> rfl

private theorem forceP6_eq {β : Sort _} (x : P6) (k : P6 → β) : forceP6 x k = k x := by
  simp only [forceP6, force_eq]

private def Tid : P6 := tab (fun k => k) 0 49 z6
private def Tsq : P6 := tab (fun k => gfMul k k) 0 49 z6
private def Tnp : P6 := tab (fun k => gfNeg (gfMul (k / 49) (k % 49))) 0 2401 z6
private def U1 : P6 := joinP (constP 1 117649 0) z6 z6 z6
private def U2 : P6 := joinP (mapP (fun p => spread p 2401 49) 6 Tid) (constP 1 2401 12) z6 z6
private def Ua : P6 := mapP (fun p => spread p 49 2401) 18 Tnp
private def Ub : P6 := mapP (fun p => rep p 49 2401) 24 Tsq
private def U4 : P6 := joinP ⟨ladd Ua.re Ub.re, ladd Ua.im Ub.im⟩
  (mapP (fun p => spread p 49 49) 30 Tid) (constP 1 49 36) z6
private def U5 : P6 := joinP (mapP (fun p => rep (spread p 49 49) 2401 49) 42 Tid)
  (mapP (fun p => rep p 49 49) 48 Tsq) Tid (constP 1 1 54)
private def U6 : P6 :=
  joinP (mapP (fun p => rep p 49 2401) 60 Tid) (mapP (fun p => rep p 49 49) 66 Tid) z6 z6

private theorem withU_eq {β : Sort _} (k : P6 → P6 → P6 → P6 → P6 → β) :
    withU k = k U1 U2 U4 U5 U6 := by
  simp only [withU, tabK_eq, coordsK, forceP6_eq, laddK_eq]
  rfl

private theorem lz6_Tid : LZ6 Tid 49 := lz6_tab _ _
private theorem lz6_Tsq : LZ6 Tsq 49 := lz6_tab _ _
private theorem lz6_Tnp : LZ6 Tnp 2401 := lz6_tab _ _

private theorem lv6_Tid {L : Nat} (hL : L < 49) : lv6 Tid L = gfDec L := lv6_tab hL hL
private theorem lv6_Tsq {L : Nat} (hL : L < 49) : lv6 Tsq L = gfDec (gfMul L L) :=
  lv6_tab hL (gfMul_lt _ _)
private theorem lv6_Tnp {L : Nat} (hL : L < 2401) :
    lv6 Tnp L = gfDec (gfNeg (gfMul (L / 49) (L % 49))) := lv6_tab hL (gfNeg_lt _)

private theorem lv6_ladd6 (a b : P6) (L : Nat) :
    lv6 ⟨ladd a.re b.re, ladd a.im b.im⟩ L = lv6 a L + lv6 b L := by
  ext
  · simp only [lv6, lv_ladd, QuadraticAlgebra.re_add]
  · simp only [lv6, lv_ladd, QuadraticAlgebra.im_add]

private theorem lz6_ladd6 {a b : P6} {w : Nat} (ha : LZ6 a w) (hb : LZ6 b w) :
    LZ6 ⟨ladd a.re b.re, ladd a.im b.im⟩ w := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := hb
  exact ⟨fun L hL => (bt_ladd_zero (a0 L hL) (a1 L hL) (a2 L hL) (b0 L hL) (b1 L hL) (b2 L hL)).1,
    fun L hL => (bt_ladd_zero (a0 L hL) (a1 L hL) (a2 L hL) (b0 L hL) (b1 L hL) (b2 L hL)).2.1,
    fun L hL => (bt_ladd_zero (a0 L hL) (a1 L hL) (a2 L hL) (b0 L hL) (b1 L hL) (b2 L hL)).2.2,
    fun L hL => (bt_ladd_zero (a3 L hL) (a4 L hL) (a5 L hL) (b3 L hL) (b4 L hL) (b5 L hL)).1,
    fun L hL => (bt_ladd_zero (a3 L hL) (a4 L hL) (a5 L hL) (b3 L hL) (b4 L hL) (b5 L hL)).2.1,
    fun L hL => (bt_ladd_zero (a3 L hL) (a4 L hL) (a5 L hL) (b3 L hL) (b4 L hL) (b5 L hL)).2.2⟩

private theorem lv6_U1 {L : Nat} (hL : L < NL) : lv6 U1 L = gfDec (laneArgs L).1 := by
  unfold NL at hL
  rw [U1, lv6_joinP (lz6_constP 1 117649 0) (lz6_z6 _) (lz6_z6 _)]
  unfold laneArgs
  split_ifs with h1 h2 h3
  · exact lv6_constP (by norm_num) h1
  · rw [lv6_z6, gfDec_zero]
  · rw [lv6_z6, gfDec_zero]
  · rw [lv6_z6, gfDec_zero]

private theorem lv6_U2 {L : Nat} (hL : L < NL) : lv6 U2 L = gfDec (laneArgs L).2.1 := by
  unfold NL at hL
  rw [U2, lv6_joinP (lz6_spread lz6_Tid (by norm_num)) (lz6_constP 1 2401 12) (lz6_z6 _)]
  unfold laneArgs
  split_ifs with h1 h2 h3
  · rw [lv6_spread lz6_Tid (by omega), lv6_Tid (by omega)]
  · exact lv6_constP (by norm_num) (by omega)
  · rw [lv6_z6, gfDec_zero]
  · rw [lv6_z6, gfDec_zero]

private theorem lv6_U4 {L : Nat} (hL : L < NL) : lv6 U4 L = gfDec (laneArgs L).2.2.1 := by
  unfold NL at hL
  have hUa : LZ6 Ua 117649 := lz6_spread lz6_Tnp (by norm_num)
  have hUb : LZ6 Ub 117649 := lz6_rep lz6_Tsq (by norm_num)
  rw [U4, lv6_joinP (lz6_ladd6 hUa hUb) (lz6_spread lz6_Tid (by norm_num)) (lz6_constP 1 49 36)]
  unfold laneArgs
  split_ifs with h1 h2 h3
  · rw [lv6_ladd6, gfDec_add, Ua, Ub, lv6_spread lz6_Tnp (by omega), lv6_Tnp (by omega),
      lv6_rep lz6_Tsq (by omega), lv6_Tsq (by omega), show L / 49 / 49 = L / 2401 by omega]
  · rw [lv6_spread lz6_Tid (by omega), lv6_Tid (by omega)]
  · exact lv6_constP (by norm_num) (by omega)
  · rw [lv6_z6, gfDec_zero]

private theorem lv6_U5 {L : Nat} (hL : L < NL) : lv6 U5 L = gfDec (laneArgs L).2.2.2.1 := by
  unfold NL at hL
  rw [U5, lv6_joinP (lz6_rs lz6_Tid) (lz6_rep lz6_Tsq (by norm_num)) lz6_Tid]
  unfold laneArgs
  split_ifs with h1 h2 h3
  · rw [lv6_rs lz6_Tid h1, lv6_Tid (by omega), show L % 2401 / 49 = L / 49 % 49 by omega]
  · rw [lv6_rep lz6_Tsq (by omega), lv6_Tsq (by omega)]
  · exact lv6_Tid (by omega)
  · exact lv6_constP (by norm_num) (by omega)

private theorem lv6_U6 {L : Nat} (hL : L < NL) : lv6 U6 L = gfDec (laneArgs L).2.2.2.2 := by
  unfold NL at hL
  rw [U6, lv6_joinP (lz6_rep lz6_Tid (by norm_num)) (lz6_rep lz6_Tid (by norm_num)) (lz6_z6 _)]
  unfold laneArgs
  split_ifs with h1 h2 h3
  · rw [lv6_rep lz6_Tid (by omega), lv6_Tid (by omega)]
  · rw [lv6_rep lz6_Tid (by omega), lv6_Tid (by omega)]
  · rw [lv6_z6, gfDec_zero]
  · rw [lv6_z6, gfDec_zero]

private theorem laneArgs_lt (L : Nat) : (laneArgs L).1 < 49 ∧ (laneArgs L).2.1 < 49 ∧
    (laneArgs L).2.2.1 < 49 ∧ (laneArgs L).2.2.2.1 < 49 ∧ (laneArgs L).2.2.2.2 < 49 := by
  unfold laneArgs
  split_ifs with h1 h2 h3 <;> dsimp only
  · exact ⟨by norm_num, by omega, gfAdd_lt _ _, by omega, by omega⟩
  · exact ⟨by norm_num, by norm_num, by omega, gfMul_lt _ _, by omega⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, by omega, by norm_num⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

private theorem lt49_laneVec (c : N7) (L : Nat) : Lt49 (laneVec c L) := by
  obtain ⟨h1, h2, h4, h5, h6⟩ := laneArgs_lt L
  exact lt49_candN h1 h2 h4 h5 h6

private def ofR (r : ZMod 7) : GF49 := ⟨r, 0⟩

private theorem re_ofR (r : ZMod 7) : (ofR r).re = r := rfl

private theorem ofR_inj {r s : ZMod 7} : ofR r = ofR s ↔ r = s := by
  rw [QuadraticAlgebra.ext_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

private theorem ofR_eq_zero {r : ZMod 7} : ofR r = 0 ↔ r = 0 := by
  rw [QuadraticAlgebra.ext_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

private theorem ofR_mul (r s : ZMod 7) : ofR r * ofR s = ofR (r * s) := by
  apply QuadraticAlgebra.ext
  · simp only [ofR, QuadraticAlgebra.re_mul]
    ring
  · simp only [ofR, QuadraticAlgebra.im_mul]
    ring

private theorem ofR_sub (r s : ZMod 7) : ofR r - ofR s = ofR (r - s) := by
  apply QuadraticAlgebra.ext
  · simp only [ofR, QuadraticAlgebra.re_sub]
  · simp only [ofR, QuadraticAlgebra.im_sub, sub_zero]

private theorem mul_star' (z : GF49) : z * star z = ofR (nrm z) := by
  apply QuadraticAlgebra.ext
  · simp only [ofR, nrm, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star,
      QuadraticAlgebra.im_star]
    ring
  · simp only [ofR, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring

private theorem mk_zero : (⟨0, 0⟩ : GF49) = 0 := rfl

private theorem herC_im (x : V7) : (herC x x).im = 0 := by
  simp only [herC, bfC, tauC, conj49, QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
    QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat]
  ring

private theorem herC_self {x : V7} (h3 : x.x3 = 0) :
    herC x x = ofR (nrm x.x0 + nrm x.x1 + nrm x.x2 + nrm x.x4 + nrm x.x5 + 5 * nrm x.x6) := by
  have h5 : (5 : ZMod 7) = -2 := by decide
  rw [h5]
  apply QuadraticAlgebra.ext
  · simp only [herC, bfC, tauC, conj49, h3, ofR, nrm, QuadraticAlgebra.re_add,
      QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_ofNat,
      QuadraticAlgebra.im_ofNat, QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
    ring
  · rw [herC_im]
    rfl

private theorem herC_ofR (x : N7) : herC x.dec x.dec = ofR ((herN x x % 7 : Nat) : ZMod 7) := by
  apply QuadraticAlgebra.ext
  · rw [← herN_dec, gfDec_re, natCast_mod_seven, re_ofR]
  · rw [herC_im]
    rfl

private theorem bne_of_iff {a b : Nat} {X : ZMod 7} (h : a = b ↔ X = 0) :
    (a != b) = !decide (X = 0) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, h]
  simp

private theorem vtxF_eq {c b : N7} (hc : Lt49 c) (hb : Lt49 b) {H r : ZMod 7}
    (hH : herC b.dec b.dec = ofR H) (hr : herC c.dec c.dec = ofR r) :
    vtxF c (herN c c) b (hDiag b) = ((!decide (H = 0) && !decide (H + -nrm b.dec.x0 = 0)) &&
      !decide (r * H + -nrm (herC c.dec b.dec) = 0)) := by
  have hβ : hDiag b < 49 := hDiag_lt b
  have dβ : gfDec (hDiag b) = ofR H := (hDiag_dec hb).trans hH
  have h1 : hDiag b = 0 ↔ H = 0 := by
    rw [eq_iff_dec hβ (by norm_num : (0 : Nat) < 49), dβ, gfDec_zero, ofR_eq_zero]
  have h2 : hDiag b = fNorm b.x0 ↔ H + -nrm b.dec.x0 = 0 := by
    rw [eq_iff_dec hβ (fNorm_lt _), dβ, fNorm_eq hb.1, gfDec_mul, gfDec_conj, mul_star', ofR_inj,
      ← sub_eq_add_neg, sub_eq_zero]
    rfl
  have h3 : fMul (herN c c) (hDiag b) = fNorm (hF c b) ↔
      r * H + -nrm (herC c.dec b.dec) = 0 := by
    rw [eq_iff_dec (fMul_lt _ _) (fNorm_lt _), fMul_eq (herN_lt c c) hβ, fNorm_eq (hF_lt c b),
      gfDec_mul, gfDec_mul, gfDec_conj, herN_dec, dβ, hF_dec hc hb, mul_star', hr, ofR_mul,
      ofR_inj, ← sub_eq_add_neg, sub_eq_zero]
  unfold vtxF
  rw [bne_of_iff h1, bne_of_iff h2, bne_of_iff h3]

private theorem colC_eq {x y : V7} {H r : ZMod 7} (hx : herC x x = ofR H) (hy : herC y y = ofR r) :
    colC x y = (!decide (r * H + -nrm (herC x y) = 0) && decide (bfC x y = 0)) := by
  have hg : gramC x y = ofR (r * H + -nrm (herC x y)) := by
    rw [gramC, hx, hy, herC_swap x y, mul_star', ofR_mul, ofR_sub]
    congr 1
    ring
  rw [colC, hg, Bool.and_comm, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ofR_eq_zero, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]

private def u0Of (c : N7) : P6 :=
  linA none none (b0Coef (tbP MM U1) (tbP MM U2) (tbP MM U4) (tbP MM U5) (tbP MM U6) c)

private def hOf (c : N7) : P3 := herUU MM (u0Of c) U1 U2 U4 U5 U6

private def tabsOf (c : N7) : Tabs :=
  ⟨tbP MM (u0Of c), tbP MM U1, tbP MM U2, tbP MM U4, tbP MM U5, tbP MM U6, tbl MM (hOf c)⟩

private def vOf (c : N7) : Nat := vtxM MM (tabsOf c) (u0Of c) (hOf c) c

private theorem rowCore_eq (c : N7) (rootL : Nat) (lvls : List (List Nat)) :
    rowCore c rootL lvls = ((vOf c).testBit (rootL + 64) &&
      match runLv MM (tabsOf c) (vOf c) c (2 ^ (rootL + 64)) lvls with
      | none => false
      | some S => Nat.land (vOf c) (Nat.xor S MM) >>> 64 == 0) := by
  unfold rowCore
  simp only [force_eq, withU_eq, tbPK_eq, linK_eq, herUUK_eq, tblK_eq, vtxMK_eq]
  rfl

private theorem lvo_none (L : Nat) : lvo none L = 0 := by
  simp only [lvo, Option.getD_none, lv_z3]

private theorem dec_x0 (x : N7) : x.dec.x0 = gfDec x.x0 := rfl
private theorem dec_x1 (x : N7) : x.dec.x1 = gfDec x.x1 := rfl
private theorem dec_x2 (x : N7) : x.dec.x2 = gfDec x.x2 := rfl
private theorem dec_x3 (x : N7) : x.dec.x3 = gfDec x.x3 := rfl
private theorem dec_x4 (x : N7) : x.dec.x4 = gfDec x.x4 := rfl
private theorem dec_x5 (x : N7) : x.dec.x5 = gfDec x.x5 := rfl
private theorem dec_x6 (x : N7) : x.dec.x6 = gfDec x.x6 := rfl

private theorem laneVec_x3 (c : N7) (L : Nat) : (laneVec c L).x3 = 0 := rfl

private theorem lv6_Us {c : N7} {L : Nat} (hL : L < NL) :
    lv6 U1 L = gfDec (laneVec c L).x1 ∧ lv6 U2 L = gfDec (laneVec c L).x2 ∧
      lv6 U4 L = gfDec (laneVec c L).x4 ∧ lv6 U5 L = gfDec (laneVec c L).x5 ∧
      lv6 U6 L = gfDec (laneVec c L).x6 :=
  ⟨lv6_U1 hL, lv6_U2 hL, lv6_U4 hL, lv6_U5 hL, lv6_U6 hL⟩

private theorem tbOk_U {L : Nat} (hm : bt MM L = true) (l : List (Tb × Nat))
    (hl : ∀ ta ∈ l, ∃ x, ta.1 = tbP MM x) : ∀ ta ∈ l, TbOk ta.1 L := by
  intro ta hta
  obtain ⟨x, hx⟩ := hl ta hta
  rw [hx]
  exact tbP_ok hm

private theorem lv6_u0 {c : N7} {L : Nat} (hL : L < NL) :
    lv6 (u0Of c) L = gfDec (laneVec c L).x0 := by
  obtain ⟨e1, e2, e4, e5, e6⟩ := lv6_Us (c := c) hL
  rw [u0Of, lv6_linA none none _ (tbOk_U (bt_MM hL) _ (by
    intro ta hta
    simp only [b0Coef, List.mem_cons, List.not_mem_nil, or_false] at hta
    rcases hta with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩))]
  simp only [b0Coef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tv_tbP, lvo_none,
    mk_zero, zero_add, add_zero, e1, e2, e4, e5, e6]
  simp only [laneVec, candN, gfDec_neg, gfDec_add, gfDec_mul, gfDec_kappa]
  ring

private theorem lv_hOf {c : N7} {L : Nat} (hL : L < NL) :
    lv (hOf c) L = nrm (laneVec c L).dec.x0 + nrm (laneVec c L).dec.x1 +
      nrm (laneVec c L).dec.x2 + nrm (laneVec c L).dec.x4 + nrm (laneVec c L).dec.x5 +
      5 * nrm (laneVec c L).dec.x6 := by
  obtain ⟨e1, e2, e4, e5, e6⟩ := lv6_Us (c := c) hL
  rw [hOf, lv_herUU (bt_MM hL), lv6_u0 hL, e1, e2, e4, e5, e6]
  rfl

private theorem herC_lane {c : N7} {L : Nat} (hL : L < NL) :
    herC (laneVec c L).dec (laneVec c L).dec = ofR (lv (hOf c) L) := by
  rw [lv_hOf hL]
  exact herC_self (by rw [dec_x3, laneVec_x3, gfDec_zero])

private theorem lv6_hc {c : N7} {L : Nat} (hL : L < NL) :
    lv6 (linCA none none (hcCoef (tabsOf c) c)) L = herC c.dec (laneVec c L).dec := by
  obtain ⟨e1, e2, e4, e5, e6⟩ := lv6_Us (c := c) hL
  rw [lv6_linCA none none _ (tbOk_U (bt_MM hL) _ (by
    intro ta hta
    simp only [hcCoef, tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hta
    rcases hta with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩))]
  simp only [hcCoef, tabsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tv_tbP,
    lvo_none, mk_zero, zero_add, add_zero, lv6_u0 hL, e1, e2, e4, e5, e6]
  simp only [herC, bfC, tauC, conj49, dec_x0, dec_x1, dec_x2, dec_x3, dec_x4, dec_x5, dec_x6,
    laneVec_x3, gfDec_zero, star_zero, zero_mul, add_zero, gfDec_mul, gfDec_kappa]
  ring

private theorem lv6_her {c v : N7} {L : Nat} (hL : L < NL) :
    lv6 (linA none none (herCoef (tabsOf c) v)) L = herC (laneVec c L).dec v.dec := by
  obtain ⟨e1, e2, e4, e5, e6⟩ := lv6_Us (c := c) hL
  rw [lv6_linA none none _ (tbOk_U (bt_MM hL) _ (by
    intro ta hta
    simp only [herCoef, tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hta
    rcases hta with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩))]
  simp only [herCoef, tabsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tv_tbP,
    lvo_none, mk_zero, zero_add, add_zero, lv6_u0 hL, e1, e2, e4, e5, e6]
  simp only [herC, bfC, tauC, conj49, dec_x0, dec_x1, dec_x2, dec_x3, dec_x4, dec_x5, dec_x6,
    laneVec_x3, gfDec_zero, mul_zero, add_zero, gfDec_mul, gfDec_kappa, gfDec_conj]
  ring

private theorem lv6_bf {c v : N7} {L : Nat} (hL : L < NL) :
    lv6 (linA none none (bfCoef (tabsOf c) v)) L = bfC (laneVec c L).dec v.dec := by
  obtain ⟨e1, e2, e4, e5, e6⟩ := lv6_Us (c := c) hL
  rw [lv6_linA none none _ (tbOk_U (bt_MM hL) _ (by
    intro ta hta
    simp only [bfCoef, tabsOf, List.mem_cons, List.not_mem_nil, or_false] at hta
    rcases hta with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩))]
  simp only [bfCoef, tabsOf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, tv_tbP,
    lvo_none, mk_zero, zero_add, add_zero, lv6_u0 hL, e1, e2, e4, e5, e6]
  simp only [bfC, dec_x0, dec_x1, dec_x2, dec_x3, dec_x4, dec_x5, dec_x6,
    laneVec_x3, gfDec_zero, mul_zero, add_zero, gfDec_mul, gfDec_kappa]
  ring

private theorem lv_sum_nsq {m L : Nat} (hm : bt m L = true) (h : P3) (x : P6) :
    lv (sumP (h :: nsq m x)) L = lv h L + -nrm (lv6 x L) := by
  rw [lv_sumP, List.map_cons, List.sum_cons, sum_nsq hm]

private theorem lv_sum_gram {m L g : Nat} (hm : bt m L = true) (hg : g < 7) (h : P3) (x : P6) :
    lv (sumP ((addP none (tbl m h) g).toList ++ nsq m x)) L =
      (g : ZMod 7) * lv h L + -nrm (lv6 x L) := by
  rw [lv_sumP, List.map_append, List.sum_append, sum_toList, sum_nsq hm, lvo_addP (tbl_ok hm) hg,
    lvo_none, zero_add, sel_tbl_one]

private theorem decide_lv6 (X : P6) (L : Nat) :
    (decide (lv X.re L = 0) && decide (lv X.im L = 0)) = decide (lv6 X L = 0) := by
  rw [← Bool.decide_and]
  exact decide_eq_decide.2 (by rw [QuadraticAlgebra.ext_iff]; rfl)

private theorem bt_vOf {c : N7} (hc : Lt49 c) {L : Nat} (hL : L < NL) :
    bt (vOf c) L = vtxF c (herN c c) (laneVec c L) (hDiag (laneVec c L)) := by
  have hm := bt_MM hL
  rw [vtxF_eq hc (lt49_laneVec c L) (herC_lane hL) (herC_ofR c), vOf, vtxM,
    show (tabsOf c).th = tbl MM (hOf c) from rfl, bt_land, bt_land, bt_nz hm, bt_nz hm, bt_nz hm,
    lv_sum_nsq hm, lv_sum_gram hm (Nat.mod_lt _ (by norm_num)), lv6_u0 hL, lv6_hc hL]
  rfl

private theorem bt_adjM {c v : N7} {L : Nat} (hL : L < NL) :
    bt (adjM MM (tabsOf c) v) L = colN (laneVec c L) v := by
  have hm := bt_MM hL
  have hcol : colN (laneVec c L) v = colC (laneVec c L).dec v.dec := by
    rw [Bool.eq_iff_iff, colN_iff]
  rw [hcol, colC_eq (herC_lane hL) (herC_ofR v), adjM,
    show (tabsOf c).th = tbl MM (hOf c) from rfl, bt_land, bt_land, bt_nz hm, bt_lzero hm,
    bt_lzero hm, decide_lv6, lv_sum_gram hm (Nat.mod_lt _ (by norm_num)), lv6_her hL, lv6_bf hL]

private def Vx (c : N7) (L : Nat) : Prop :=
  vtxF c (herN c c) (laneVec c L) (hDiag (laneVec c L)) = true

private def Rch (c r : N7) (k L : Nat) : Prop :=
  ∃ n, n ≤ k ∧ Wk colN (fun u => ∃ L' < NL, u = laneVec c L' ∧ Vx c L') n r (laneVec c L)

private def Inv (c r : N7) (k S : Nat) : Prop := ∀ L < NL, bt S L = true → Rch c r k L

private theorem Inv.mono {c r : N7} {k S : Nat} (h : Inv c r k S) : Inv c r (k + 1) S :=
  fun L hL hS => by
    obtain ⟨n, hn, w⟩ := h L hL hS
    exact ⟨n, by omega, w⟩

private theorem stepL_inv {c : N7} (hc : Lt49 c) {r : N7} {k S : Nat} (hS : Inv c r k S) :
    ∀ (Ls : List Nat) (a S' : Nat), Inv c r (k + 1) a →
      stepL MM (tabsOf c) (vOf c) S c Ls a = some S' → Inv c r (k + 1) S'
  | [], a, S', ha, h => by
    rw [stepL, Option.some.injEq] at h
    subst h
    exact ha
  | L :: Ls, a, S', ha, h => by
    rw [stepL_cons] at h
    cases hb : (S.testBit (L + 64) && decide (L < NL))
    · rw [hb, cond_false] at h
      exact absurd h (by simp)
    · rw [hb, cond_true] at h
      rw [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨hSL, hL⟩ := hb
      refine stepL_inv hc hS Ls _ S' ?_ h
      intro L' hL' hbt
      rw [bt_xor_mix, bt_lor, bt_land, bt_vOf hc hL', bt_adjM hL', Bool.or_eq_true,
        Bool.and_eq_true] at hbt
      rcases hbt with h1 | ⟨hv, hcol⟩
      · exact ha L' hL' h1
      · obtain ⟨n, hn, w⟩ := hS L hL hSL
        exact ⟨n + 1, by omega, w.snoc (colN_symm hcol) ⟨L', hL', rfl, hv⟩⟩

private theorem runLv_inv {c : N7} (hc : Lt49 c) {r : N7} :
    ∀ (lvls : List (List Nat)) (k S S' : Nat), Inv c r k S →
      runLv MM (tabsOf c) (vOf c) c S lvls = some S' → Inv c r (k + lvls.length) S'
  | [], k, S, S', hS, h => by
    rw [runLv, Option.some.injEq] at h
    subst h
    exact hS
  | Ls :: rest, k, S, S', hS, h => by
    cases hst : stepL MM (tabsOf c) (vOf c) S c Ls S with
    | none => simp only [runLv, hst, reduceCtorEq] at h
    | some S1 =>
      simp only [runLv, hst, force_eq] at h
      have h1 := runLv_inv hc rest (k + 1) S1 S' (stepL_inv hc hS Ls S S1 hS.mono hst) h
      rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
      simpa only [Nat.add_right_comm] using h1

theorem rowCore_spec {c : N7} (hc : Lt49 c) {rootL : Nat} {lvls : List (List Nat)}
    (hr : rootL < NL) (h : rowCore c rootL lvls = true) :
    vtxF c (herN c c) (laneVec c rootL) (hDiag (laneVec c rootL)) = true ∧
      ∀ L < NL, vtxF c (herN c c) (laneVec c L) (hDiag (laneVec c L)) = true → ∃ n,
        n ≤ lvls.length ∧ Wk colN (fun u => ∃ L' < NL, u = laneVec c L' ∧
          vtxF c (herN c c) (laneVec c L') (hDiag (laneVec c L')) = true) n (laneVec c rootL)
          (laneVec c L) := by
  rw [rowCore_eq, Bool.and_eq_true] at h
  obtain ⟨hroot, hrun⟩ := h
  have hroot' : bt (vOf c) rootL = true := hroot
  rw [bt_vOf hc hr] at hroot'
  refine ⟨hroot', fun L hL hv => ?_⟩
  revert hrun
  cases hR : runLv MM (tabsOf c) (vOf c) c (2 ^ (rootL + 64)) lvls with
  | none => intro hfin; simp at hfin
  | some S =>
    intro hfin
    have hz : Nat.land (vOf c) (Nat.xor S MM) >>> 64 = 0 := by simpa using hfin
    have h0 : Inv c (laneVec c rootL) 0 (2 ^ (rootL + 64)) := by
      intro L' _ hb
      rw [bt_two_pow, decide_eq_true_eq] at hb
      subst hb
      exact ⟨0, le_refl 0, Wk.nil _⟩
    have hinv := runLv_inv hc lvls 0 _ S h0 hR
    have hbit : bt (Nat.land (vOf c) (Nat.xor S MM)) L = false := by
      unfold bt
      rw [Nat.add_comm, ← Nat.testBit_shiftRight, hz, Nat.zero_testBit]
    rw [bt_land, bt_xor, bt_MM hL, bt_vOf hc hL, hv, Bool.true_and, Bool.xor_true,
      Bool.not_eq_false'] at hbit
    obtain ⟨n, hn, w⟩ := hinv L hL hbit
    exact ⟨n, by omega, w⟩

end CFSG.Certificates.Kernel.Q7Bits.Lanes
