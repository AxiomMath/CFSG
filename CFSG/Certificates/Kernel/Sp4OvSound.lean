module

public import Certificates.Data.Kernel.Sp4Ov.Special
public import CFSG.Quasithin.H13.L32NSp4Code

public section

namespace CFSG.KD.Sp4Ov

open CFSG.Quasithin.H13 Sp4Cert KGCert

@[expose] def dec (c : ℕ) : List ℕ := [c % 16, c / 16 % 16, c / 256 % 16, c / 4096 % 16]

theorem validC4_dec (c : ℕ) : ValidC4 (dec c) := by
  refine ⟨rfl, fun x hx => ?_⟩
  simp only [dec, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by norm_num)

theorem codeC_dec {c : ℕ} (hc : c < 65536) : codeC (dec c) = c := by
  simp only [codeC, dec, List.getD_cons_zero, List.getD_cons_succ]
  omega

theorem dec_codeC {x : List ℕ} (hx : ValidC4 x) : dec (codeC x) = x := by
  obtain ⟨hl, hlt⟩ := hx
  match x, hl with
  | [a, b, c, d], _ =>
    have ha := hlt a (by simp)
    have hb := hlt b (by simp)
    have hc := hlt c (by simp)
    have hd := hlt d (by simp)
    simp only [dec, codeC, List.getD_cons_zero, List.getD_cons_succ, List.cons.injEq, and_true]
    omega

theorem dec_inj {c d : ℕ} (hc : c < 65536) (hd : d < 65536) (h : dec c = dec d) : c = d := by
  rw [← codeC_dec hc, ← codeC_dec hd, h]

theorem nib (a n : ℕ) : a >>> n &&& 15 = a / 2 ^ n % 16 := by
  have h15 : (15 : ℕ) = 2 ^ 4 - 1 := rfl
  rw [Nat.shiftRight_eq_div_pow, h15, Nat.and_two_pow_sub_one_eq_mod]

theorem bit1 (v k : ℕ) : v >>> k &&& 1 = if v.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h <;> simp [h]

theorem mv_def (a v : ℕ) : mv a v =
    ((a >>> 0 &&& 15) * (v >>> 0 &&& 1) ^^^ (a >>> 4 &&& 15) * (v >>> 1 &&& 1)) ^^^
      ((a >>> 8 &&& 15) * (v >>> 2 &&& 1) ^^^ (a >>> 12 &&& 15) * (v >>> 3 &&& 1)) := rfl

theorem mv_eq (a v : ℕ) : mv a v = mulVecC (dec a) v := by
  rw [mv_def]
  simp only [nib, bit1, mul_ite, mul_one, mul_zero, mulVecC, dec, bt, List.getD_cons_zero,
    List.getD_cons_succ, List.getD_nil, ite_self, Nat.xor_zero, Nat.xor_assoc]
  norm_num

theorem mv_lt (a v : ℕ) : mv a v < 16 := by
  have hn : ∀ n, a >>> n &&& 15 < 2 ^ 4 := fun n => by rw [nib]; exact Nat.mod_lt _ (by norm_num)
  have hm : ∀ n k, (a >>> n &&& 15) * (v >>> k &&& 1) < 2 ^ 4 := fun n k => by
    rw [bit1]
    split_ifs
    · simpa using hn n
    · simp
  have h16 : (16 : ℕ) = 2 ^ 4 := rfl
  rw [mv_def, h16]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hm _ _) (hm _ _))
    (Nat.xor_lt_two_pow (hm _ _) (hm _ _))

theorem mulP_def (a b : ℕ) : mulP a b =
    (mv a (b >>> 0 &&& 15) ||| mv a (b >>> 4 &&& 15) <<< 4) |||
      (mv a (b >>> 8 &&& 15) <<< 8 ||| mv a (b >>> 12 &&& 15) <<< 12) := rfl

theorem pack {m0 m1 m2 m3 : ℕ} (h0 : m0 < 16) (h1 : m1 < 16) (h2 : m2 < 16) (h3 : m3 < 16) :
    (m0 ||| m1 <<< 4) ||| (m2 <<< 8 ||| m3 <<< 12) = m0 + 16 * m1 + 256 * m2 + 4096 * m3 := by
  have e1 : m0 ||| m1 <<< 4 = m0 + 16 * m1 := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : m0 < 2 ^ 4), Nat.shiftLeft_eq]
    ring
  have e2 : (m0 + 16 * m1) ||| m2 <<< 8 = m0 + 16 * m1 + 256 * m2 := by
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega : m0 + 16 * m1 < 2 ^ 8),
      Nat.shiftLeft_eq]
    ring
  have e3 : (m0 + 16 * m1 + 256 * m2) ||| m3 <<< 12 =
      m0 + 16 * m1 + 256 * m2 + 4096 * m3 := by
    rw [Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega : m0 + 16 * m1 + 256 * m2 < 2 ^ 12),
      Nat.shiftLeft_eq]
    ring
  rw [← Nat.or_assoc, e1, e2, e3]

theorem dec_mulP (c d : ℕ) : dec (mulP c d) = mulC (dec c) (dec d) := by
  have hd : ∀ m0 m1 m2 m3 : ℕ, m0 < 16 → m1 < 16 → m2 < 16 → m3 < 16 →
      dec (m0 + 16 * m1 + 256 * m2 + 4096 * m3) = [m0, m1, m2, m3] := by
    intro m0 m1 m2 m3 h0 h1 h2 h3
    simp only [dec, List.cons.injEq, and_true]
    omega
  rw [mulP_def, pack (mv_lt _ _) (mv_lt _ _) (mv_lt _ _) (mv_lt _ _),
    hd _ _ _ _ (mv_lt _ _) (mv_lt _ _) (mv_lt _ _) (mv_lt _ _)]
  simp only [nib, mv_eq, mulC, dec, List.map_cons, List.map_nil]
  norm_num

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bJK_eq : ∀ u < 16, ∀ w < 16, bJK u w = (if bJ u w then 1 else 0) := by
  decide +kernel

theorem bJ_symm : ∀ u < 16, ∀ w < 16, bJ w u = bJ u w := by decide +kernel

theorem bJ_self : ∀ u < 16, bJ u u = false := by decide +kernel

theorem col0 (c : ℕ) : col c 0 = c % 16 := (nib c 0).trans (by norm_num)

theorem col1 (c : ℕ) : col c 1 = c / 16 % 16 := (nib c 4).trans (by norm_num)

theorem col2 (c : ℕ) : col c 2 = c / 256 % 16 := (nib c 8).trans (by norm_num)

theorem col3 (c : ℕ) : col c 3 = c / 4096 % 16 := (nib c 12).trans (by norm_num)

theorem isSympC_expl (a b c d : ℕ) : isSympC [a, b, c, d] =
    (((bJ a a == false) && ((bJ a b == false) && ((bJ a c == false) &&
      ((bJ a d == true) && true)))) &&
    (((bJ b a == false) && ((bJ b b == false) && ((bJ b c == true) &&
      ((bJ b d == false) && true)))) &&
    (((bJ c a == false) && ((bJ c b == true) && ((bJ c c == false) &&
      ((bJ c d == false) && true)))) &&
    (((bJ d a == true) && ((bJ d b == false) && ((bJ d c == false) &&
      ((bJ d d == false) && true)))) && true)))) := rfl

theorem isSympK_eq (c : ℕ) : isSympK c = isSympC (dec c) := by
  have h0 : c % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h1 : c / 16 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h2 : c / 256 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : c / 4096 % 16 < 16 := Nat.mod_lt _ (by norm_num)
  simp only [isSympK, bAnd_eq, col0, col1, col2, col3, dec, isSympC_expl]
  generalize c % 16 = x0 at *
  generalize c / 16 % 16 = x1 at *
  generalize c / 256 % 16 = x2 at *
  generalize c / 4096 % 16 = x3 at *
  rw [bJK_eq _ h0 _ h1, bJK_eq _ h0 _ h2, bJK_eq _ h0 _ h3, bJK_eq _ h1 _ h2, bJK_eq _ h1 _ h3,
    bJK_eq _ h2 _ h3, bJ_symm _ h0 _ h1, bJ_symm _ h0 _ h2, bJ_symm _ h0 _ h3,
    bJ_symm _ h1 _ h2, bJ_symm _ h1 _ h3, bJ_symm _ h2 _ h3, bJ_self _ h0, bJ_self _ h1,
    bJ_self _ h2, bJ_self _ h3]
  cases bJ x0 x1 <;> cases bJ x0 x2 <;> cases bJ x0 x3 <;> cases bJ x1 x2 <;>
    cases bJ x1 x3 <;> cases bJ x2 x3 <;> rfl

theorem dec_oneP : dec oneP = oneC4 := rfl

@[expose] def NodeR.els (s : NodeR) : List ℕ := 33825 :: s.tree.map (· % 65536)

@[expose] def toNode (s : NodeR) : Node :=
  ⟨s.els.map dec, s.gens.map dec, s.mask, s.reps.map fun p => dec p.r⟩

@[expose] def specOf (sp : SpecR) (A B S36 S120 : List ℕ) : Spec :=
  ⟨(A.map dec, sp.2.1), (B.map dec, sp.2.2.1), (S36.map dec, sp.1), (S120.map dec, sp.2.2.2.1),
    sp.2.2.2.2⟩

theorem memP_eq (m c : ℕ) : memP m c = m.testBit c := by
  change Nat.blt 0 (m &&& (1 <<< c)) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  cases hb : m.testBit c
  · have h0 : m &&& 2 ^ c = 0 := Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : c = j
      · subst hj
        simp [hb]
      · simp [hj]
    rw [h0]
    rfl
  · have hne : m &&& 2 ^ c ≠ 0 := fun h0 => by
      have := congrArg (fun n => n.testBit c) h0
      simp [Nat.testBit_and, hb] at this
    simpa [Nat.blt_eq] using Nat.pos_of_ne_zero hne

def planeRep (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 ^ e * planeRep e n + 1

theorem planeRep_mul (e n : ℕ) : planeRep e n * (2 ^ e - 1) = 2 ^ (e * n) - 1 := by
  induction n with
  | zero => simp [planeRep]
  | succ n ih =>
    rw [planeRep, Nat.add_mul, Nat.mul_assoc, ih, Nat.one_mul, Nat.mul_sub_one, ← Nat.pow_add,
      Nat.mul_succ, Nat.add_comm (e * n) e]
    have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
    have h3 : 2 ^ e ≤ 2 ^ (e + e * n) := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    generalize 2 ^ e = a at *
    generalize 2 ^ (e + e * n) = b at *
    omega

theorem testBit_planeRep_mul {e B : ℕ} (hB : B < 2 ^ e) (n c : ℕ) :
    (planeRep e n * B).testBit c = (decide (c < e * n) && B.testBit (c % e)) := by
  induction n generalizing c with
  | zero => simp [planeRep]
  | succ n ih =>
    rw [planeRep, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, Nat.testBit_two_pow_mul_add _ hB]
    split_ifs with hc
    · have : c < e * (n + 1) := lt_of_lt_of_le hc (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      simp [Nat.mod_eq_of_lt hc, this]
    · rw [ih, ← Nat.mod_eq_sub_mod (by omega : c ≥ e)]
      congr 1
      exact decide_eq_decide.mpr (by rw [Nat.mul_succ]; omega)

theorem plane_testBit {k : ℕ} (hk : k < 16) (c : ℕ) :
    (plane k).testBit c = (decide (c < 65536) && c.testBit k) := by
  have e : plane k = (2 ^ 65536 - 1) / (2 ^ (2 * 2 ^ k) - 1) * ((2 ^ 2 ^ k - 1) * 2 ^ 2 ^ k) := by
    change (1 <<< 65536 - 1) / (1 <<< (2 <<< k) - 1) * ((1 <<< (1 <<< k) - 1) <<< (1 <<< k)) = _
    simp only [Nat.one_shiftLeft, Nat.shiftLeft_eq, Nat.one_mul]
  have hen : 2 * 2 ^ k * 2 ^ (15 - k) = 65536 := by
    rw [← Nat.pow_succ', ← Nat.pow_add]
    have : k + 1 + (15 - k) = 16 := by omega
    rw [this]
  have hq : (2 ^ 65536 - 1) / (2 ^ (2 * 2 ^ k) - 1) = planeRep (2 * 2 ^ k) (2 ^ (15 - k)) := by
    apply Nat.div_eq_of_eq_mul_left (Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by positivity)))
    rw [planeRep_mul, hen]
  have hB : (2 ^ 2 ^ k - 1) * 2 ^ 2 ^ k < 2 ^ (2 * 2 ^ k) := by
    rw [two_mul, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by positivity) one_pos) (by positivity)
  rw [e, hq, testBit_planeRep_mul hB, hen, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  interval_cases k <;> norm_num <;> omega

theorem bJK_eq_ite (u w : ℕ) : bJK u w = if ((u.testBit 0 && w.testBit 3) ^^
    (u.testBit 3 && w.testBit 0)) ^^ ((u.testBit 1 && w.testBit 2) ^^
      (u.testBit 2 && w.testBit 1)) then 1 else 0 := by
  have e : bJK u w = ((((u &&& w >>> 3) ^^^ (u >>> 3 &&& w)) ^^^
      ((u >>> 1 &&& w >>> 2) ^^^ (u >>> 2 &&& w >>> 1))) >>> 0) &&& 1 := rfl
  rw [e, bit1]
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero,
    Nat.zero_add]

theorem bJK_lt (u w : ℕ) : bJK u w < 2 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem col_testBit (c i t : ℕ) : (col c i).testBit t = (decide (t < 4) && c.testBit (i <<< 2 + t)) := by
  change (c >>> (i <<< 2) &&& 15).testBit t = _
  have h15 : (15 : ℕ) = 2 ^ 4 - 1 := rfl
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h15, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem bJPl_testBit {i j : ℕ} (hi : i < 4) (hj : j < 4) (c : ℕ) :
    (bJPl i j).testBit c = (decide (c < 65536) && decide (bJK (col c i) (col c j) = 1)) := by
  have e : bJPl i j = ((plane (i <<< 2) &&& plane (j <<< 2 + 3)) ^^^
      (plane (i <<< 2 + 3) &&& plane (j <<< 2))) ^^^ ((plane (i <<< 2 + 1) &&&
        plane (j <<< 2 + 2)) ^^^ (plane (i <<< 2 + 2) &&& plane (j <<< 2 + 1))) := rfl
  have hi' : i <<< 2 < 13 := by rw [Nat.shiftLeft_eq]; omega
  have hj' : j <<< 2 < 13 := by rw [Nat.shiftLeft_eq]; omega
  rw [e, bJK_eq_ite]
  simp only [Nat.testBit_xor, Nat.testBit_and, col_testBit,
    plane_testBit (by omega : i <<< 2 < 16), plane_testBit (by omega : i <<< 2 + 1 < 16),
    plane_testBit (by omega : i <<< 2 + 2 < 16), plane_testBit (by omega : i <<< 2 + 3 < 16),
    plane_testBit (by omega : j <<< 2 < 16), plane_testBit (by omega : j <<< 2 + 1 < 16),
    plane_testBit (by omega : j <<< 2 + 2 < 16), plane_testBit (by omega : j <<< 2 + 3 < 16),
    Nat.add_zero]
  generalize decide (c < 65536) = d
  generalize c.testBit (i <<< 2) = b0
  generalize c.testBit (i <<< 2 + 1) = b1
  generalize c.testBit (i <<< 2 + 2) = b2
  generalize c.testBit (i <<< 2 + 3) = b3
  generalize c.testBit (j <<< 2) = d0
  generalize c.testBit (j <<< 2 + 1) = d1
  generalize c.testBit (j <<< 2 + 2) = d2
  generalize c.testBit (j <<< 2 + 3) = d3
  revert d b0 b1 b2 b3 d0 d1 d2 d3
  decide

theorem elemsOK_sound {spM : ℕ} (h : elemsOK spM = true) (c : ℕ) :
    memP spM c = true ↔ c < 65536 ∧ isSympK c = true := by
  have hs : sympMaskK = spM := Nat.eq_of_beq_eq_true h
  have hA : allP.testBit c = decide (c < 65536) := by
    change (1 <<< 65536 - 1).testBit c = _
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]
  have e : sympMaskK = ((bJPl 0 1 ^^^ allP) &&& (bJPl 0 2 ^^^ allP)) &&&
      ((bJPl 0 3 &&& bJPl 1 2) &&& ((bJPl 1 3 ^^^ allP) &&& (bJPl 2 3 ^^^ allP))) := rfl
  rw [← hs, memP_eq, e]
  have p : ∀ i j : ℕ, i < 4 → j < 4 → ∀ c, (bJPl i j).testBit c =
      (decide (c < 65536) && decide (bJK (col c i) (col c j) = 1)) :=
    fun _ _ hi hj => bJPl_testBit hi hj
  simp only [Nat.testBit_and, Nat.testBit_xor, hA, p 0 1 (by norm_num) (by norm_num),
    p 0 2 (by norm_num) (by norm_num), p 0 3 (by norm_num) (by norm_num),
    p 1 2 (by norm_num) (by norm_num), p 1 3 (by norm_num) (by norm_num),
    p 2 3 (by norm_num) (by norm_num), isSympK, bAnd_eq]
  have b01 := bJK_lt (col c 0) (col c 1)
  have b02 := bJK_lt (col c 0) (col c 2)
  have b03 := bJK_lt (col c 0) (col c 3)
  have b12 := bJK_lt (col c 1) (col c 2)
  have b13 := bJK_lt (col c 1) (col c 3)
  have b23 := bJK_lt (col c 2) (col c 3)
  generalize bJK (col c 0) (col c 1) = x01 at *
  generalize bJK (col c 0) (col c 2) = x02 at *
  generalize bJK (col c 0) (col c 3) = x03 at *
  generalize bJK (col c 1) (col c 2) = x12 at *
  generalize bJK (col c 1) (col c 3) = x13 at *
  generalize bJK (col c 2) (col c 3) = x23 at *
  obtain rfl | rfl : x01 = 0 ∨ x01 = 1 := by omega
  all_goals obtain rfl | rfl : x02 = 0 ∨ x02 = 1 := by omega
  all_goals obtain rfl | rfl : x03 = 0 ∨ x03 = 1 := by omega
  all_goals obtain rfl | rfl : x12 = 0 ∨ x12 = 1 := by omega
  all_goals obtain rfl | rfl : x13 = 0 ∨ x13 = 1 := by omega
  all_goals obtain rfl | rfl : x23 = 0 ∨ x23 = 1 := by omega
  all_goals by_cases hc : c < 65536 <;> simp [hc] <;> rfl

open CFSG.KC.Loop in
theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem bNot_true {a : Bool} (h : Bool.rec (motive := fun _ => Bool) true false a = true) :
    a = false := by
  cases a
  · rfl
  · exact absurd h Bool.false_ne_true

theorem bRec_mem {α : Type} {f : α → Bool} {l : List α}
    (h : List.rec (motive := fun _ => Bool) true
      (fun p _ ih => Bool.rec (motive := fun _ => Bool) false ih (f p)) l = true) :
    ∀ p ∈ l, f p = true := by
  induction l with
  | nil => intro p hp; cases hp
  | cons a t ih =>
    obtain ⟨h1, h2⟩ := bAnd_true h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h1
    · exact ih h2 p hp

theorem fld16 (e : ℕ) : Nat.land (Nat.shiftRight e 0) 65535 = e % 65536 := by
  have h : (65535 : ℕ) = 2 ^ 16 - 1 := rfl
  change e >>> 0 &&& 65535 = _
  rw [Nat.shiftRight_zero, h, Nat.and_two_pow_sub_one_eq_mod]

theorem subP_bit {m m' : ℕ} (h : subP m m' = true) {c : ℕ} (hc : m.testBit c = true) :
    m'.testBit c = true := by
  have h1 : m &&& m' = m := Nat.eq_of_beq_eq_true h
  have := congrArg (fun n => n.testBit c) h1
  simp only [Nat.testBit_and, hc, Bool.true_and] at this
  exact this

theorem mulP_lt (a b : ℕ) : mulP a b < 65536 := by
  rw [mulP_def, pack (mv_lt _ _) (mv_lt _ _) (mv_lt _ _) (mv_lt _ _)]
  have h0 := mv_lt a (b >>> 0 &&& 15)
  have h1 := mv_lt a (b >>> 4 &&& 15)
  have h2 := mv_lt a (b >>> 8 &&& 15)
  have h3 := mv_lt a (b >>> 12 &&& 15)
  omega

theorem codeC_lt {x : List ℕ} (hx : ValidC4 x) : codeC x < 65536 := by
  have h0 := getD_lt hx 0
  have h1 := getD_lt hx 1
  have h2 := getD_lt hx 2
  have h3 := getD_lt hx 3
  unfold codeC
  omega

theorem memL_mem {l : List ℕ} {g : ℕ} (h : memL l g = true) : g ∈ l := by
  induction l with
  | nil => exact absurd h Bool.false_ne_true
  | cons a t ih =>
    have e : memL (a :: t) g = Bool.rec (motive := fun _ => Bool) (memL t g) true (Nat.beq a g) :=
      rfl
    rw [e] at h
    cases hb : Nat.beq a g
    · rw [hb] at h
      exact List.mem_cons.mpr (Or.inr (ih h))
    · exact List.mem_cons.mpr (Or.inl (Nat.eq_of_beq_eq_true hb).symm)

theorem getN_mem (L : List NodeR) (i : ℕ) : getN L i ∈ L ∨ getN L i = nodeZ := by
  induction L generalizing i with
  | nil => exact Or.inr rfl
  | cons a t ih =>
    cases i with
    | zero => exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
    | succ j =>
      rcases ih j with h' | h'
      · exact Or.inl (List.mem_cons.mpr (Or.inr h'))
      · exact Or.inr h'

theorem treeStep_ne {gens : List ℕ} {m e : ℕ} (h : treeStep gens m e ≠ 0) :
    memP m (e >>> 16 &&& 65535) = true ∧ memP m (e % 65536) = false ∧
      memL gens (e >>> 32) = true ∧ mulP (e >>> 16 &&& 65535) (e >>> 32) = e % 65536 ∧
      treeStep gens m e = m ||| 1 <<< (e % 65536) := by
  have he : treeStep gens m e = Bool.rec (motive := fun _ => ℕ) 0
      (m ||| 1 <<< Nat.land (Nat.shiftRight e 0) 65535)
      (Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (Nat.beq (mulP (e >>> 16 &&& 65535) (e >>> 32)) (Nat.land (Nat.shiftRight e 0) 65535))
          (memL gens (e >>> 32)))
        (Bool.rec (motive := fun _ => Bool) true false (memP m (Nat.land (Nat.shiftRight e 0) 65535))))
      (memP m (e >>> 16 &&& 65535))) := rfl
  rw [fld16] at he
  rw [he] at h ⊢
  revert h
  generalize e >>> 16 &&& 65535 = z
  generalize e >>> 32 = g
  generalize e % 65536 = y
  cases h1 : memP m z <;> cases h2 : memP m y <;> cases h3 : memL gens g <;>
    cases h4 : Nat.beq (mulP z g) y <;> intro h <;>
    first
    | exact (h rfl).elim
    | exact ⟨rfl, rfl, rfl, Nat.eq_of_beq_eq_true h4, rfl⟩

theorem treeK_cons (gens tr : List ℕ) (m e : ℕ) :
    treeK gens (e :: tr) m = treeK gens tr (treeStep gens m e) :=
  strictN_eq _ (treeK gens tr)

theorem treeStep_zero (gens : List ℕ) (e : ℕ) : treeStep gens 0 e = 0 := by
  by_contra h
  have h1 := (treeStep_ne h).1
  rw [memP_eq, Nat.zero_testBit] at h1
  exact Bool.false_ne_true h1

theorem treeK_zero (gens : List ℕ) : ∀ tr, treeK gens tr 0 = 0
  | [] => rfl
  | e :: tr => by rw [treeK_cons, treeStep_zero, treeK_zero gens tr]

theorem treeK_spec (gens : List ℕ) (Q : ℕ → Prop)
    (hQ : ∀ z g, Q z → memL gens g = true → Q (mulP z g)) :
    ∀ (tr : List ℕ) (m : ℕ), treeK gens tr m ≠ 0 → (∀ c, m.testBit c = true → Q c) →
      treeK gens tr m = tr.foldl (fun m e => m ||| 1 <<< (e % 65536)) m ∧
      (tr.map (· % 65536)).Nodup ∧ (∀ y ∈ tr.map (· % 65536), m.testBit y = false) ∧
      ∀ y ∈ tr.map (· % 65536), Q y
  | [], m, _, _ => ⟨rfl, List.nodup_nil, by simp, by simp⟩
  | e :: tr, m, hne, hm => by
    rw [treeK_cons] at hne ⊢
    have hs : treeStep gens m e ≠ 0 := fun h0 => hne (by rw [h0, treeK_zero])
    obtain ⟨h1, h2, h3, h4, h5⟩ := treeStep_ne hs
    rw [h5] at hne ⊢
    have hy : Q (e % 65536) := by
      rw [← h4]
      exact hQ _ _ (hm _ (by rwa [memP_eq] at h1)) h3
    have hbit : ∀ c, (m ||| 1 <<< (e % 65536)).testBit c =
        (m.testBit c || decide (e % 65536 = c)) := by
      intro c
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    have hm' : ∀ c, (m ||| 1 <<< (e % 65536)).testBit c = true → Q c := by
      intro c hc
      rw [hbit, Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | rfl
      · exact hm c hc
      · exact hy
    obtain ⟨i1, i2, i3, i4⟩ := treeK_spec gens Q hQ tr _ hne hm'
    refine ⟨i1, ?_, ?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, i2⟩
      have := i3 _ hmem
      rw [hbit] at this
      simp at this
    · intro y hy'
      rw [List.map_cons, List.mem_cons] at hy'
      rcases hy' with rfl | hy'
      · rwa [memP_eq] at h2
      · have := i3 y hy'
        rw [hbit, Bool.or_eq_false_iff] at this
        exact this.1
    · intro y hy'
      rw [List.map_cons, List.mem_cons] at hy'
      rcases hy' with rfl | hy'
      · exact hy
      · exact i4 y hy'

theorem foldl_addM_dec : ∀ (l : List ℕ), (∀ c ∈ l, c < 65536) → ∀ m,
    (l.map dec).foldl addM m = l.foldl (fun m c => m ||| 1 <<< c) m
  | [], _, _ => rfl
  | c :: l, hl, m => by
    rw [List.map_cons, List.foldl_cons, List.foldl_cons,
      foldl_addM_dec l (fun x hx => hl x (List.mem_cons.mpr (Or.inr hx))), addM,
      codeC_dec (hl c (List.mem_cons.mpr (Or.inl rfl)))]

theorem tree_facts {s : NodeR} (h1 : memP s.mask oneP = true)
    (h4 : treeK s.gens s.tree (1 <<< oneP) = s.mask) :
    s.mask = maskOf (s.els.map dec) ∧ s.els.Nodup ∧ (∀ c ∈ s.els, c < 65536) ∧
      ∀ P : List ℕ → Prop, P oneC4 → (∀ a, P a → ∀ g ∈ s.gens.map dec, P (mulC a g)) →
        ∀ c ∈ s.els, P (dec c) := by
  have hne : treeK s.gens s.tree (1 <<< oneP) ≠ 0 := by
    rw [h4]
    intro h0
    rw [h0, memP_eq, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  have h0bit : ∀ c, (1 <<< oneP).testBit c = true → c = 33825 := by
    intro c hc
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hc
    exact (of_decide_eq_true hc).symm
  obtain ⟨i1, i2, i3, -⟩ := treeK_spec s.gens (fun _ => True) (fun _ _ _ _ => trivial) s.tree _
    hne fun _ _ => trivial
  have hlt : ∀ c ∈ s.els, c < 65536 := by
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · norm_num
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hc
      exact Nat.mod_lt _ (by norm_num)
  refine ⟨?_, ?_, hlt, ?_⟩
  · rw [maskOf, foldl_addM_dec _ hlt, ← h4, i1, NodeR.els, List.foldl_cons, List.foldl_map] <;> rfl
  · rw [NodeR.els, List.nodup_cons]
    refine ⟨fun hm => ?_, i2⟩
    have := i3 _ hm
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at this
    exact absurd rfl (of_decide_eq_false this)
  · intro P hP hcl
    obtain ⟨-, -, -, i4⟩ := treeK_spec s.gens (fun c => P (dec c)) (fun z g hz hg => by
        rw [dec_mulP]
        exact hcl _ hz _ (List.mem_map_of_mem (memL_mem hg))) s.tree _ hne
      fun c hc => by rw [h0bit c hc]; exact hP
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hP
    · exact i4 c hc

theorem nodeK_parts {spM : ℕ} {L : List NodeR} {s : NodeR} (h : nodeK spM L s = true) :
    memP s.mask oneP = true ∧ subP s.mask spM = true ∧ (∀ g ∈ s.gens, memP s.mask g = true) ∧
      treeK s.gens s.tree (1 <<< oneP) = s.mask ∧ (∀ p ∈ s.reps, repOK L s.mask p = true) ∧
      (s.mask ||| covAll s.mask s.reps 0) = spM := by
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨h2, h⟩ := bAnd_true h
  obtain ⟨h3, h⟩ := bAnd_true h
  obtain ⟨h4, h⟩ := bAnd_true h
  obtain ⟨h5, h6⟩ := bAnd_true h
  exact ⟨h1, h2, bRec_mem (f := memP s.mask) h3, Nat.eq_of_beq_eq_true h4,
    bRec_mem (f := repOK L s.mask) h5, Nat.eq_of_beq_eq_true h6⟩

theorem repOK_parts {L : List NodeR} {m : ℕ} {p : RepR} (h : repOK L m p = true) :
    memP m p.r = false ∧ mulP p.ri p.r = oneP ∧ subP m (getN L p.t).mask = true ∧
      memP (getN L p.t).mask p.r = true ∧ wordsOK m p.r (getN L p.t).gens p.words = true := by
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨h3, h⟩ := bAnd_true h
  obtain ⟨h4, h⟩ := bAnd_true h
  obtain ⟨h5, h6⟩ := bAnd_true h
  exact ⟨bNot_true h1, Nat.eq_of_beq_eq_true h3, h4, h5, h6⟩

theorem evalW_cons (m r l : ℕ) (w : List ℕ) (acc : ℕ) :
    evalW m r (l :: w) acc = Bool.rec (motive := fun _ => ℕ) 1048576 (evalW m r w (mulP acc l))
      (Bool.rec (motive := fun _ => Bool) (Nat.beq l r) true (memP m l)) := rfl

theorem evalW_spec (m r : ℕ) (Q : ℕ → Prop)
    (hQ : ∀ a l, Q a → (memP m l = true ∨ l = r) → Q (mulP a l)) :
    ∀ (w : List ℕ) (acc : ℕ), evalW m r w acc ≠ 1048576 → Q acc → Q (evalW m r w acc)
  | [], _, _, hacc => hacc
  | l :: w, acc, hne, hacc => by
    rw [evalW_cons] at hne ⊢
    revert hne
    cases h1 : memP m l <;> cases h2 : Nat.beq l r <;> intro hne
    · exact (hne rfl).elim
    · exact evalW_spec m r Q hQ w (mulP acc l) hne
        (hQ _ _ hacc (Or.inr (Nat.eq_of_beq_eq_true h2)))
    · exact evalW_spec m r Q hQ w (mulP acc l) hne (hQ _ _ hacc (Or.inl h1))
    · exact evalW_spec m r Q hQ w (mulP acc l) hne (hQ _ _ hacc (Or.inl h1))

theorem wordsOK_spec {m r : ℕ} {gens : List ℕ} {ws : List (List ℕ)}
    (h : wordsOK m r gens ws = true) : ∀ g ∈ gens, ∃ tl, evalW m r tl oneP = g := by
  induction gens generalizing ws with
  | nil => intro g hg; cases hg
  | cons g gs ih =>
    cases ws with
    | nil => exact absurd h Bool.false_ne_true
    | cons w ws =>
      obtain ⟨hw, hrest⟩ : wordOK m r g w = true ∧ wordsOK m r gs ws = true := bAnd_true h
      intro g' hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · cases w with
        | nil => exact absurd hw Bool.false_ne_true
        | cons hd tl =>
          obtain ⟨-, h2⟩ : Nat.beq hd g' = true ∧ Nat.beq (evalW m r tl oneP) g' = true :=
            bAnd_true hw
          exact ⟨tl, Nat.eq_of_beq_eq_true h2⟩
      · exact ih hrest g' hg'

theorem covK_cons (m ri e : ℕ) (cov : List ℕ) (acc : ℕ) :
    covK m ri (e :: cov) acc = covK m ri cov (Bool.rec (motive := fun _ => ℕ) acc
      (acc ||| 1 <<< Nat.land (Nat.shiftRight e 0) 65535)
      (Bool.rec (motive := fun _ => Bool) false
        (memP m (mulP (mulP ri (e >>> 16)) (Nat.land (Nat.shiftRight e 0) 65535)))
        (memP m (e >>> 16)))) :=
  strictN_eq _ (covK m ri cov)

theorem covK_bit (m ri : ℕ) : ∀ (cov : List ℕ) (acc c : ℕ), (covK m ri cov acc).testBit c = true →
    acc.testBit c = true ∨ ∃ a, memP m a = true ∧ memP m (mulP (mulP ri a) c) = true
  | [], _, _, h => Or.inl h
  | e :: cov, acc, c, h => by
    rw [covK_cons, fld16] at h
    revert h
    cases h1 : memP m (e >>> 16) <;>
      cases h2 : memP m (mulP (mulP ri (e >>> 16)) (e % 65536)) <;> intro h
    · exact covK_bit m ri cov acc c h
    · exact covK_bit m ri cov acc c h
    · exact covK_bit m ri cov acc c h
    · rcases covK_bit m ri cov (acc ||| 1 <<< (e % 65536)) c h with h' | h'
      · rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq] at h'
        rcases h' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨_, h1, h2⟩
      · exact Or.inr h'

theorem covAll_cons (m : ℕ) (p : RepR) (ps : List RepR) (acc : ℕ) :
    covAll m (p :: ps) acc = covAll m ps (covK m p.ri p.cover acc) :=
  strictN_eq _ (covAll m ps)

theorem covAll_bit (m : ℕ) : ∀ (reps : List RepR) (acc c : ℕ),
    (covAll m reps acc).testBit c = true → acc.testBit c = true ∨
      ∃ p ∈ reps, ∃ a, memP m a = true ∧ memP m (mulP (mulP p.ri a) c) = true
  | [], _, _, h => Or.inl h
  | p :: ps, acc, c, h => by
    rw [covAll_cons] at h
    rcases covAll_bit m ps _ c h with h' | ⟨q, hq, h'⟩
    · rcases covK_bit m p.ri p.cover acc c h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr ⟨p, List.mem_cons.mpr (Or.inl rfl), h''⟩
    · exact Or.inr ⟨q, List.mem_cons.mpr (Or.inr hq), h'⟩

theorem nodeK_sound {spM : ℕ} {L : List NodeR} (he : elemsOK spM = true) (h : ovK spM L = true)
    {s : NodeR} (hs : s ∈ L) :
    (toNode s).mask = maskOf (toNode s).els ∧ (toNode s).els.Nodup ∧
      (∀ x ∈ (toNode s).els, isSympC x = true) ∧
      (∀ g ∈ (toNode s).gens, memM (toNode s).mask g = true) ∧
      (∀ P : List ℕ → Prop, P oneC4 → (∀ a, P a → ∀ g ∈ (toNode s).gens, P (mulC a g)) →
        ∀ x ∈ (toNode s).els, P x) ∧
      (∀ r ∈ (toNode s).reps, memM (toNode s).mask r = false) ∧
      (∀ x ∈ spElsC, memM (toNode s).mask x = true ∨ ∃ r ∈ (toNode s).reps, ∃ ri, ValidC4 ri ∧
        mulC ri r = oneC4 ∧ ∃ a ∈ (toNode s).els, memM (toNode s).mask (mulC (mulC ri a) x) = true) ∧
      ∀ r ∈ (toNode s).reps, ∃ t ∈ L, subM (toNode s).mask (toNode t).mask = true ∧
        memM (toNode t).mask r = true ∧
        ∀ P : List ℕ → Prop, P oneC4 →
          (∀ a, P a → ∀ l, (l ∈ (toNode s).els ∨ l = r) → P (mulC a l)) →
          ∀ g ∈ (toNode t).gens, P g := by
  have hnode : ∀ t ∈ L, nodeK spM L t = true := bRec_mem (f := nodeK spM L) h
  have hb : ∀ {m : ℕ}, subP m spM = true → ∀ c, m.testBit c = true → c < 65536 := fun hs c hc =>
    ((elemsOK_sound he c).mp (by rw [memP_eq]; exact subP_bit hs hc)).1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := nodeK_parts (hnode s hs)
  obtain ⟨hmask, hnd, hlt, hgen⟩ := tree_facts h1 h4
  have hin : ∀ c ∈ s.els, s.mask.testBit c = true := fun c hc => by
    have := memM_maskOf_of_mem (List.mem_map_of_mem hc : dec c ∈ s.els.map dec)
    rwa [← hmask, memM, codeC_dec (hlt c hc)] at this
  have hmemb : ∀ c, s.mask.testBit c = true → dec c ∈ s.els.map dec := fun c hc => by
    have hc' := hb h2 c hc
    have : memM (maskOf (s.els.map dec)) (dec c) = true := by
      rw [← hmask, memM, codeC_dec hc']
      exact hc
    obtain ⟨y, hy, hyc⟩ := memM_maskOf.mp this
    obtain ⟨c', hc'', rfl⟩ := List.mem_map.mp hy
    rw [codeC_dec (hlt c' hc''), codeC_dec hc'] at hyc
    rw [← hyc]
    exact List.mem_map_of_mem hc''
  have hrep : ∀ p ∈ s.reps, p.r < 65536 ∧ getN L p.t ∈ L ∧ memP s.mask p.r = false ∧
      mulP p.ri p.r = oneP ∧ subP s.mask (getN L p.t).mask = true ∧
      memP (getN L p.t).mask p.r = true ∧ wordsOK s.mask p.r (getN L p.t).gens p.words = true := by
    intro p hp
    obtain ⟨r1, r2, r3, r4, r5⟩ := repOK_parts (h5 p hp)
    have htL : getN L p.t ∈ L := by
      rcases getN_mem L p.t with h' | h'
      · exact h'
      · rw [h', memP_eq] at r4
        simp [nodeZ, NodeR.mask] at r4
    obtain ⟨-, t2, -, -, -, -⟩ := nodeK_parts (hnode _ htL)
    exact ⟨hb t2 _ (by rwa [memP_eq] at r4), htL, r1, r2, r3, r4, r5⟩
  refine ⟨hmask, hnd.map_on fun x hx y hy hxy => dec_inj (hlt x hx) (hlt y hy) hxy, ?_, ?_,
    fun P hP hcl x hx => ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    rw [← isSympK_eq]
    exact ((elemsOK_sound he c).mp (by rw [memP_eq]; exact subP_bit h2 (hin c hc))).2
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    have := h3 g hg
    rw [memP_eq] at this
    rw [memM, codeC_dec (hb h2 g this)]
    exact this
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact hgen P hP hcl c hc
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hr, -, r1, -⟩ := hrep p hp
    rw [memM, codeC_dec hr, ← memP_eq]
    exact r1
  · intro x hx
    obtain ⟨hv, hsy⟩ := mem_spElsC.mp hx
    have hc := codeC_lt hv
    have hxc : x = dec (codeC x) := (dec_codeC hv).symm
    have hsp : spM.testBit (codeC x) = true := by
      rw [← memP_eq]
      exact (elemsOK_sound he _).mpr ⟨hc, by rw [isSympK_eq, ← hxc]; exact hsy⟩
    rw [← h6, Nat.testBit_or, Bool.or_eq_true] at hsp
    rcases hsp with hm | hcv
    · exact Or.inl hm
    · rcases covAll_bit s.mask s.reps 0 _ hcv with h0 | ⟨p, hp, a, ha, hra⟩
      · rw [Nat.zero_testBit] at h0
        exact absurd h0 Bool.false_ne_true
      · obtain ⟨-, -, -, r2, -⟩ := hrep p hp
        refine Or.inr ⟨dec p.r, List.mem_map_of_mem hp, dec p.ri, validC4_dec _, ?_, dec a,
          hmemb a (by rwa [memP_eq] at ha), ?_⟩
        · rw [← dec_mulP, r2]
          rfl
        · rw [hxc, ← dec_mulP, ← dec_mulP, memM, codeC_dec (mulP_lt _ _), ← memP_eq]
          exact hra
  · intro r hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    obtain ⟨hr, htL, -, -, r3, r4, r5⟩ := hrep p hp
    obtain ⟨-, t2, t3, -, -, -⟩ := nodeK_parts (hnode _ htL)
    refine ⟨getN L p.t, htL, subM_iff.mpr fun c hc => subP_bit r3 hc, ?_, ?_⟩
    · rw [memM, codeC_dec hr, ← memP_eq]
      exact r4
    · intro P hP hcl x hx
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
      obtain ⟨tl, htl⟩ := wordsOK_spec r5 g hg
      have hg' : g < 65536 := hb t2 g (by rw [← memP_eq]; exact t3 g hg)
      have := evalW_spec s.mask p.r (fun c => P (dec c)) (fun a l ha hl => by
          rw [dec_mulP]
          refine hcl _ ha _ ?_
          rcases hl with hl | rfl
          · exact Or.inl (hmemb l (by rwa [memP_eq] at hl))
          · exact Or.inr rfl) tl oneP (by rw [htl]; omega) hP
      rw [htl] at this
      exact this

theorem bOr_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) b true a = true) :
    a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem bOr_intro {a b : Bool} (h : a = true ∨ b = true) :
    Bool.rec (motive := fun _ => Bool) b true a = true := by
  cases a
  · exact h.resolve_left Bool.false_ne_true
  · rfl

theorem bIf_true {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem imp_bool {c r : Bool} (h : c = true → r = true) : (!c || r) = true := by
  cases c <;> simp_all

theorem natAll {f : ℕ → Bool} : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun a ih => Bool.rec (motive := fun _ => Bool) false ih (f a)) n = true → ∀ a < n, f a = true
  | 0, _, a, ha => absurd ha (Nat.not_lt_zero a)
  | n + 1, h, a, ha => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    by_cases hn : a = n
    · subst hn
      exact h1
    · exact natAll n h2 a (by omega)

theorem natAny {f : ℕ → Bool} : ∀ n, Nat.rec (motive := fun _ => Bool) false
    (fun v ih => Bool.rec (motive := fun _ => Bool) ih true (f v)) n = true → ∃ v < n, f v = true
  | 0, h => absurd h Bool.false_ne_true
  | n + 1, h => by
    rcases bOr_true h with h1 | h2
    · exact ⟨n, by omega, h1⟩
    · obtain ⟨v, hv, h'⟩ := natAny n h2
      exact ⟨v, by omega, h'⟩

theorem all16_spec {f : ℕ → Bool} (h : all16 f = true) : ∀ a < 16, f a = true := natAll 16 h

theorem any16_spec {f : ℕ → Bool} (h : any16 f = true) : ∃ v < 16, f v = true := natAny 16 h

theorem anyRec_mem {α : Type} {f : α → Bool} {l : List α}
    (h : List.rec (motive := fun _ => Bool) false
      (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (f p)) l = true) :
    ∃ p ∈ l, f p = true := by
  induction l with
  | nil => exact absurd h Bool.false_ne_true
  | cons a t ih =>
    rcases bOr_true h with h1 | h2
    · exact ⟨a, List.mem_cons.mpr (Or.inl rfl), h1⟩
    · obtain ⟨p, hp, h'⟩ := ih h2
      exact ⟨p, List.mem_cons.mpr (Or.inr hp), h'⟩

theorem anyRec_intro {α : Type} {f : α → Bool} {l : List α} {p : α} (hp : p ∈ l)
    (h : f p = true) : List.rec (motive := fun _ => Bool) false
      (fun p _ ih => Bool.rec (motive := fun _ => Bool) ih true (f p)) l = true := by
  induction l with
  | nil => cases hp
  | cons a t ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact bOr_intro (Or.inl h)
    · exact bOr_intro (Or.inr (ih hp))

theorem anyMems_spec {s : NodeR} {g : ℕ → Bool} (h : anyMems s.tree g = true) :
    ∃ c ∈ s.els, g c = true := by
  rcases bOr_true h with h1 | h2
  · exact ⟨33825, List.mem_cons.mpr (Or.inl rfl), h1⟩
  · obtain ⟨e, he, h'⟩ := anyRec_mem (f := fun e => g (Nat.land (Nat.shiftRight e 0) 65535)) h2
    have h'' : g (Nat.land (Nat.shiftRight e 0) 65535) = true := h'
    rw [fld16] at h''
    exact ⟨e % 65536, List.mem_cons.mpr (Or.inr (List.mem_map_of_mem he)), h''⟩

theorem sizeK_eq (s : NodeR) : sizeK s = s.els.length := by
  have key : ∀ (tr : List ℕ) (acc : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun _ _ ih acc => CFSG.KC.Loop.strictN (acc + 1) ih) tr acc = acc + tr.length := by
    intro tr
    induction tr with
    | nil => intro acc; rfl
    | cons e t ih =>
      intro acc
      rw [List.length_cons]
      exact (strictN_eq _ _).trans ((ih (acc + 1)).trans (by omega))
  have e : sizeK s = List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun _ _ ih acc => CFSG.KC.Loop.strictN (acc + 1) ih) s.tree 1 := rfl
  rw [e, key, NodeR.els, List.length_cons, List.length_map]
  omega

theorem qK_eq : ∀ a < 16, ∀ v < 16, qK a v = if qJ a v then 1 else 0 := by decide +kernel

theorem xor_facts' : ∀ u < 16, ∀ v < 16,
    u = 0 ∨ v = 0 ∨ u = v ∨ (u ^^^ v ≠ u ∧ u ^^^ v ≠ v ∧ u ^^^ v < 16) := by decide +kernel

theorem xor_facts (u : ℕ) (hu : u < 16) (v : ℕ) (hv : v < 16) (h0u : 0 < u) (h0v : 0 < v)
    (huv : u ≠ v) : u ^^^ v ≠ u ∧ u ^^^ v ≠ v ∧ u ^^^ v < 16 := by
  rcases xor_facts' u hu v hv with h | h | h | h
  · omega
  · omega
  · exact absurd h huv
  · exact h

theorem onL_spec {l z : ℕ} (h : onL l z = true) :
    z = (l >>> 0 &&& 15) ∨ z = (l >>> 4 &&& 15) ∨ z = (l >>> 8 &&& 15) := by
  have e : onL l z = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq z (l >>> 8 &&& 15)) true
        (Nat.beq z (l >>> 4 &&& 15))) true (Nat.beq z (l >>> 0 &&& 15)) := rfl
  rw [e] at h
  revert h
  cases h0 : Nat.beq z (l >>> 0 &&& 15) <;> cases h1 : Nat.beq z (l >>> 4 &&& 15) <;>
    cases h2 : Nat.beq z (l >>> 8 &&& 15) <;> intro h <;>
    first
    | exact absurd h Bool.false_ne_true
    | exact Or.inl (Nat.eq_of_beq_eq_true h0)
    | exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h1))
    | exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h2))

theorem qZero_true {a u v l : ℕ} (ha : a < 16) (hu : u < 16) (hv : v < 16) (h0u : 0 < u)
    (h0v : 0 < v) (huv : u ≠ v) (hl : isLine u v l = true) (hqu : qJ a u = false)
    (hqv : qJ a v = false) (hqw : qJ a (u ^^^ v) = false) : qZero a l = true := by
  obtain ⟨h1, h⟩ := bAnd_true hl
  obtain ⟨h2, h3⟩ := bAnd_true h
  obtain ⟨hwu, hwv, hw⟩ := xor_facts u hu v hv h0u h0v huv
  have o1 := onL_spec h1
  have o2 := onL_spec h2
  have o3 := onL_spec (z := u ^^^ v) h3
  have hb : ∀ k, l >>> k &&& 15 < 16 := fun k => lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have hz : ∀ f, f < 16 → (f = u ∨ f = v ∨ f = u ^^^ v) → qK a f = 0 := by
    intro f hf hfo
    rw [qK_eq a ha f hf]
    rcases hfo with rfl | rfl | rfl
    · simp [hqu]
    · simp [hqv]
    · simp [hqw]
  have e : qZero a l = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq (qK a (l >>> 8 &&& 15)) 0)
        (Nat.beq (qK a (l >>> 4 &&& 15)) 0)) (Nat.beq (qK a (l >>> 0 &&& 15)) 0) := rfl
  have b0 := hb 0
  have b1 := hb 4
  have b2 := hb 8
  generalize l >>> 0 &&& 15 = F0 at *
  generalize l >>> 4 &&& 15 = F1 at *
  generalize l >>> 8 &&& 15 = F2 at *
  generalize u ^^^ v = w at *
  rw [e, hz F0 b0 (by omega), hz F1 b1 (by omega), hz F2 b2 (by omega)] <;> rfl

theorem mem_tiLinesC {l : List ℕ} (hl : l ∈ tiLinesC) : ∃ u < 16, ∃ v < 16, 0 < u ∧ 0 < v ∧
    u ≠ v ∧ bJ u v = false ∧ l = [u, v, u ^^^ v] := by
  simp only [tiLinesC, List.mem_flatMap, List.mem_range, List.mem_filterMap,
    Option.ite_none_right_eq_some, Option.some.injEq] at hl
  obtain ⟨u, hu, v, hv, hc, rfl⟩ := hl
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hc
  exact ⟨u, hu, v, hv, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, rfl⟩

theorem lines_spec {lines : List ℕ} (h : linesOK lines = true) {u v : ℕ} (hu : u < 16)
    (hv : v < 16) (h0u : 0 < u) (h0v : 0 < v) (huv : u ≠ v) (hbj : bJ u v = false) :
    ∃ l ∈ lines, isLine u v l = true := by
  have hG := all16_spec (all16_spec h u hu) v hv
  have e1 : Nat.blt 0 u = true := by rw [Nat.blt_eq]; exact h0u
  have e2 : Nat.blt 0 v = true := by rw [Nat.blt_eq]; exact h0v
  have e3 : Nat.beq u v = false := by
    cases hb : Nat.beq u v
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) huv
  have e4 : Nat.beq (bJK u v) 0 = true := by rw [bJK_eq _ hu _ hv, hbj] <;> rfl
  have hc : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq (bJK u v) 0)
        (Bool.rec (motive := fun _ => Bool) true false (Nat.beq u v))) (Nat.blt 0 v))
      (Nat.blt 0 u) = true := by
    rw [e1, e2, e3, e4] <;> rfl
  exact anyRec_mem (bIf_true hG hc)

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem bOrT_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = (a || b) := by
  cases a <;> rfl

theorem nIf_eq (b : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t b = if b then t else e := by
  cases b <;> rfl

theorem onL_eq (l z : ℕ) : onL l z =
    decide (z = (l >>> 0 &&& 15) ∨ z = (l >>> 4 &&& 15) ∨ z = (l >>> 8 &&& 15)) := by
  have e : onL l z = Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq z (l >>> 8 &&& 15)) true
        (Nat.beq z (l >>> 4 &&& 15))) true (Nat.beq z (l >>> 0 &&& 15)) := rfl
  rw [e, bOrT_eq, bOrT_eq, beq_dec, beq_dec, beq_dec]
  simp only [Bool.decide_or]

theorem stabK_eq (x l : ℕ) : stabK x l = (onL l (mv x (l >>> 0 &&& 15)) &&
    (onL l (mv x (l >>> 4 &&& 15)) && onL l (mv x (l >>> 8 &&& 15)))) := by
  have e : stabK x l = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (onL l (mv x (l >>> 8 &&& 15)))
        (onL l (mv x (l >>> 4 &&& 15)))) (onL l (mv x (l >>> 0 &&& 15))) := rfl
  rw [e, bAnd_eq, bAnd_eq]

theorem fixK_eq (x l : ℕ) : fixK x l = (decide (mv x (l >>> 0 &&& 15) = (l >>> 0 &&& 15)) &&
    (decide (mv x (l >>> 4 &&& 15) = (l >>> 4 &&& 15)) &&
      decide (mv x (l >>> 8 &&& 15) = (l >>> 8 &&& 15)))) := by
  have e : fixK x l = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false (Nat.beq (mv x (l >>> 8 &&& 15)) (l >>> 8 &&& 15))
        (Nat.beq (mv x (l >>> 4 &&& 15)) (l >>> 4 &&& 15)))
      (Nat.beq (mv x (l >>> 0 &&& 15)) (l >>> 0 &&& 15)) := rfl
  rw [e, bAnd_eq, bAnd_eq, beq_dec, beq_dec, beq_dec]

theorem tri_all (P : ℕ → Prop) (a0 a1 a2 : ℕ) :
    (P a0 ∧ P a1 ∧ P a2) ↔ ∀ z, (z = a0 ∨ z = a1 ∨ z = a2) → P z := by
  constructor
  · rintro ⟨h0, h1, h2⟩ z (rfl | rfl | rfl) <;> assumption
  · intro h
    exact ⟨h _ (Or.inl rfl), h _ (Or.inr (Or.inl rfl)), h _ (Or.inr (Or.inr rfl))⟩

theorem line_set {u v L0 : ℕ} (hu : u < 16) (hv : v < 16) (h0u : 0 < u) (h0v : 0 < v)
    (huv : u ≠ v) (hl : isLine u v L0 = true) (z : ℕ) :
    (z = (L0 >>> 0 &&& 15) ∨ z = (L0 >>> 4 &&& 15) ∨ z = (L0 >>> 8 &&& 15)) ↔
      (z = u ∨ z = v ∨ z = u ^^^ v) := by
  obtain ⟨h1, h⟩ := bAnd_true hl
  obtain ⟨h2, h3⟩ := bAnd_true h
  obtain ⟨hwu, hwv, -⟩ := xor_facts u hu v hv h0u h0v huv
  have o1 := onL_spec h1
  have o2 := onL_spec h2
  have o3 := onL_spec (z := u ^^^ v) h3
  generalize L0 >>> 0 &&& 15 = F0 at *
  generalize L0 >>> 4 &&& 15 = F1 at *
  generalize L0 >>> 8 &&& 15 = F2 at *
  generalize u ^^^ v = w at *
  constructor <;> intro hz <;> omega

theorem stab_eq {u v L0 : ℕ} (hu : u < 16) (hv : v < 16) (h0u : 0 < u) (h0v : 0 < v)
    (huv : u ≠ v) (hl : isLine u v L0 = true) (c : ℕ) :
    stabK c L0 = [u, v, u ^^^ v].all fun y => [u, v, u ^^^ v].contains (mulVecC (dec c) y) := by
  have hT := line_set hu hv h0u h0v huv hl
  rw [Bool.eq_iff_iff]
  have e1 : stabK c L0 = true ↔ ∀ z, (z = (L0 >>> 0 &&& 15) ∨ z = (L0 >>> 4 &&& 15) ∨
      z = (L0 >>> 8 &&& 15)) → (mv c z = (L0 >>> 0 &&& 15) ∨ mv c z = (L0 >>> 4 &&& 15) ∨
        mv c z = (L0 >>> 8 &&& 15)) := by
    refine Iff.trans ?_ (tri_all (fun z => mv c z = (L0 >>> 0 &&& 15) ∨
      mv c z = (L0 >>> 4 &&& 15) ∨ mv c z = (L0 >>> 8 &&& 15)) _ _ _)
    rw [stabK_eq]
    simp only [onL_eq, Bool.and_eq_true, decide_eq_true_eq]
  have e2 : ([u, v, u ^^^ v].all fun y => [u, v, u ^^^ v].contains (mulVecC (dec c) y)) = true ↔
      ∀ z, (z = u ∨ z = v ∨ z = u ^^^ v) → (mulVecC (dec c) z = u ∨ mulVecC (dec c) z = v ∨
        mulVecC (dec c) z = u ^^^ v) := by
    refine Iff.trans ?_ (tri_all (fun z => mulVecC (dec c) z = u ∨ mulVecC (dec c) z = v ∨
      mulVecC (dec c) z = u ^^^ v) _ _ _)
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.contains_iff_mem,
      List.mem_cons, List.not_mem_nil, or_false]
  rw [e1, e2]
  simp only [hT, mv_eq]

theorem fix_eq {u v L0 : ℕ} (hu : u < 16) (hv : v < 16) (h0u : 0 < u) (h0v : 0 < v)
    (huv : u ≠ v) (hl : isLine u v L0 = true) (c : ℕ) :
    fixK c L0 = [u, v, u ^^^ v].all fun y => mulVecC (dec c) y == y := by
  have hT := line_set hu hv h0u h0v huv hl
  rw [Bool.eq_iff_iff]
  have e1 : fixK c L0 = true ↔ ∀ z, (z = (L0 >>> 0 &&& 15) ∨ z = (L0 >>> 4 &&& 15) ∨
      z = (L0 >>> 8 &&& 15)) → mv c z = z := by
    refine Iff.trans ?_ (tri_all (fun z => mv c z = z) _ _ _)
    rw [fixK_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
  have e2 : ([u, v, u ^^^ v].all fun y => mulVecC (dec c) y == y) = true ↔
      ∀ z, (z = u ∨ z = v ∨ z = u ^^^ v) → mulVecC (dec c) z = z := by
    refine Iff.trans ?_ (tri_all (fun z => mulVecC (dec c) z = z) _ _ _)
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  rw [e1, e2]
  simp only [hT, mv_eq]

theorem isNT_eq (x : List ℕ) (l : List ℕ) : isNT x l = !(l.all fun y => mulVecC x y == y) := by
  unfold isNT
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.any_cons, List.all_cons, ih, Bool.not_and, bne]

theorem beqP {c d : ℕ} (hc : c < 65536) (hd : d < 65536) : Nat.beq c d = (dec c == dec d) := by
  rw [beq_dec, Bool.eq_iff_iff, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun h => by rw [h], dec_inj hc hd⟩

theorem ord3K_eq {c : ℕ} (hc : c < 65536) : ord3K c = ord3 (dec c) := by
  have e : ord3K c = Bool.rec (motive := fun _ => Bool) (Nat.beq (mulP c (mulP c c)) oneP) false
      (Nat.beq c oneP) := rfl
  rw [e, beqP hc (by decide), beqP (mulP_lt _ _) (by decide), dec_mulP, dec_mulP, dec_oneP, ord3,
    bne]
  cases dec c == oneC4 <;> rfl

theorem invlK_eq {c : ℕ} (hc : c < 65536) : invlK c = invl (dec c) := by
  have e : invlK c = Bool.rec (motive := fun _ => Bool) (Nat.beq (mulP c c) oneP) false
      (Nat.beq c oneP) := rfl
  rw [e, beqP hc (by decide), beqP (mulP_lt _ _) (by decide), dec_mulP, dec_oneP, invl, bne]
  cases dec c == oneC4 <;> rfl

theorem memM_dec (m : ℕ) {c : ℕ} (hc : c < 65536) : memM m (dec c) = memP m c := by
  rw [memM, codeC_dec hc, memP_eq]

theorem commK_eq (f x : ℕ) : commK f x = (mulC (dec f) (dec x) == mulC (dec x) (dec f)) := by
  rw [commK, beqP (mulP_lt _ _) (mulP_lt _ _), dec_mulP, dec_mulP]

theorem foldMems_eq (s : NodeR) (f : ℕ → ℕ → ℕ) (acc : ℕ) :
    foldMems s.tree f acc = s.els.foldl (fun a x => f x a) acc := by
  have key : ∀ (tr : List ℕ) (acc : ℕ), List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun e _ ih acc => CFSG.KC.Loop.strictN (f (Nat.land (Nat.shiftRight e 0) 65535) acc) ih)
      tr acc = (tr.map (· % 65536)).foldl (fun a x => f x a) acc := by
    intro tr
    induction tr with
    | nil => intro acc; rfl
    | cons e t ih =>
      intro acc
      rw [List.map_cons, List.foldl_cons, ← ih, ← fld16 e]
      exact strictN_eq _ _
  have e : foldMems s.tree f acc = List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
      (fun e _ ih acc => CFSG.KC.Loop.strictN (f (Nat.land (Nat.shiftRight e 0) 65535) acc) ih)
      s.tree (f oneP acc) := rfl
  rw [e, key, NodeR.els, List.foldl_cons]
  rfl

def cntE (a b c : ℕ) (d e : Bool) : ℕ :=
  a + 65536 * b + 4294967296 * c + 281474976710656 * (d.toNat + 2 * e.toNat)

theorem or_hi {lo : ℕ} (hlo : lo < 2 ^ 48) (k k' : ℕ) :
    (lo + 2 ^ 48 * k) ||| 2 ^ 48 * k' = lo + 2 ^ 48 * (k ||| k') := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h0 : (0 : ℕ) < 2 ^ 48 := by positivity
  rw [Nat.testBit_or, Nat.add_comm lo, Nat.add_comm lo, Nat.testBit_two_pow_mul_add _ hlo,
    Nat.testBit_two_pow_mul_add _ hlo, ← Nat.add_zero (2 ^ 48 * k'),
    Nat.testBit_two_pow_mul_add _ h0, Nat.testBit_or]
  split_ifs <;> simp

theorem cntE_or {a b c : ℕ} (ha : a < 65536) (hb : b < 65536) (hc : c < 65536) (d e o i : Bool) :
    cntE a b c d e ||| 2 ^ 48 * (o.toNat + 2 * i.toNat) = cntE a b c (d || o) (e || i) := by
  have hlo : a + 65536 * b + 4294967296 * c < 2 ^ 48 := by norm_num; omega
  have h48 : (281474976710656 : ℕ) = 2 ^ 48 := by norm_num
  unfold cntE
  rw [h48, or_hi hlo]
  congr 2
  cases d <;> cases e <;> cases o <;> cases i <;> decide

theorem cntStep_eq (l x acc : ℕ) : cntStep l x acc =
    (acc + 4294967296 + ((stabK x l).toNat + 65536 * (stabK x l && fixK x l).toNat)) |||
      2 ^ 48 * ((stabK x l && !fixK x l && ord3K x).toNat +
        2 * (stabK x l && !fixK x l && invlK x).toNat) := by
  unfold cntStep
  generalize stabK x l = s1
  generalize fixK x l = f1
  generalize ord3K x = o1
  generalize invlK x = i1
  cases s1 <;> cases f1 <;> cases o1 <;> cases i1 <;> rfl

theorem cntE_step (l x : ℕ) {a b c : ℕ} (d e : Bool) (ha : a ≤ c) (hb : b ≤ c)
    (hc : c + 1 < 65536) :
    cntStep l x (cntE a b c d e) = cntE (a + (stabK x l).toNat) (b + (stabK x l && fixK x l).toNat)
      (c + 1) (d || (stabK x l && !fixK x l && ord3K x))
      (e || (stabK x l && !fixK x l && invlK x)) := by
  have h1 := Bool.toNat_le (stabK x l)
  have h2 := Bool.toNat_le (stabK x l && fixK x l)
  have e : cntE a b c d e + 4294967296 +
      ((stabK x l).toNat + 65536 * (stabK x l && fixK x l).toNat) =
      cntE (a + (stabK x l).toNat) (b + (stabK x l && fixK x l).toNat) (c + 1) d e := by
    unfold cntE
    ring
  rw [cntStep_eq, ← cntE_or (by omega) (by omega) hc, e]

theorem cntE_congr {a b c a' b' c' : ℕ} {d e d' e' : Bool} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') (he : e = e') : cntE a b c d e = cntE a' b' c' d' e' := by
  rw [ha, hb, hc, hd, he]

theorem ite_toNat (b : Bool) : (if b = true then 1 else 0) = b.toNat := by
  cases b <;> rfl

theorem cnt_fold (l : ℕ) : ∀ (xs : List ℕ) (a b c : ℕ) (d e : Bool), a ≤ c → b ≤ c →
    c + xs.length < 65536 →
    xs.foldl (fun acc x => cntStep l x acc) (cntE a b c d e) =
      cntE (a + xs.countP fun x => stabK x l) (b + xs.countP fun x => stabK x l && fixK x l)
        (c + xs.length) (d || xs.any fun x => stabK x l && !fixK x l && ord3K x)
        (e || xs.any fun x => stabK x l && !fixK x l && invlK x)
  | [], a, b, c, d, e, _, _, _ => by simp
  | x :: xs, a, b, c, d, e, ha, hb, hc => by
    have h1 := Bool.toNat_le (stabK x l)
    have h2 := Bool.toNat_le (stabK x l && fixK x l)
    have hc' : c + 1 < 65536 := by
      rw [List.length_cons] at hc
      omega
    rw [List.foldl_cons, cntE_step l x d e ha hb hc', cnt_fold l xs _ _ _ _ _ (by omega)
      (by omega) (by rw [List.length_cons] at hc; omega)]
    simp only [List.countP_cons, List.any_cons, List.length_cons, ite_toNat]
    apply cntE_congr
    · omega
    · omega
    · omega
    · rw [Bool.or_assoc]
    · rw [Bool.or_assoc]

theorem cntK_eq {s : NodeR} (l : ℕ) (hlen : s.els.length < 65536) : cntK s l =
    cntE (s.els.countP fun x => stabK x l) (s.els.countP fun x => stabK x l && fixK x l)
      s.els.length (s.els.any fun x => stabK x l && !fixK x l && ord3K x)
      (s.els.any fun x => stabK x l && !fixK x l && invlK x) := by
  have e : cntK s l = s.els.foldl (fun a x => cntStep l x a) (cntE 0 0 0 false false) :=
    foldMems_eq s (cntStep l) 0
  rw [e, cnt_fold l s.els 0 0 0 false false le_rfl le_rfl (by omega)]
  simp

theorem cntE_fld {a b c : ℕ} {d e : Bool} (ha : a < 65536) (hb : b < 65536) (hc : c < 65536) :
    Nat.land (Nat.shiftRight (cntE a b c d e) 0) 65535 = a ∧
      Nat.land (Nat.shiftRight (cntE a b c d e) 16) 65535 = b ∧
      Nat.land (Nat.shiftRight (cntE a b c d e) 32) 65535 = c ∧
      Nat.land (Nat.shiftRight (cntE a b c d e) 48) 1 = d.toNat ∧
      Nat.land (Nat.shiftRight (cntE a b c d e) 49) 1 = e.toNat := by
  have k : ∀ x n, Nat.land (Nat.shiftRight x n) 65535 = x / 2 ^ n % 65536 := fun x n => by
    change x >>> n &&& (2 ^ 16 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  have k1 : ∀ x n, Nat.land (Nat.shiftRight x n) 1 = x / 2 ^ n % 2 := fun x n => by
    change x >>> n &&& 1 = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hd := Bool.toNat_le d
  have he := Bool.toNat_le e
  simp only [k, k1, cntE, Nat.reducePow]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem feasK_intro {c : ℕ}
    (h1 : Nat.land (Nat.shiftRight c 0) 65535 %
      Nat.gcd (Nat.land (Nat.shiftRight c 32) 65535) 16 = 0)
    (h2 : Nat.land (Nat.shiftRight c 48) 1 = 1)
    (h3 : Nat.land (Nat.shiftRight c 0) 65535 < Nat.land (Nat.shiftRight c 32) 65535)
    (h4 : Nat.land (Nat.shiftRight c 49) 1 = 1) : feasK c = true := by
  have e : feasK c = Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false (Nat.beq (Nat.land (Nat.shiftRight c 49) 1) 1)
          (Nat.blt (Nat.land (Nat.shiftRight c 0) 65535) (Nat.land (Nat.shiftRight c 32) 65535)))
        (Nat.beq (Nat.land (Nat.shiftRight c 48) 1) 1))
      (Nat.beq (Nat.land (Nat.shiftRight c 0) 65535 %
        Nat.gcd (Nat.land (Nat.shiftRight c 32) 65535) 16) 0) := rfl
  have h3' : Nat.blt (Nat.land (Nat.shiftRight c 0) 65535)
      (Nat.land (Nat.shiftRight c 32) 65535) = true := Nat.blt_eq.mpr h3
  rw [e, h1, h2, h4, h3']
  rfl

theorem conclF_cases {sp : SpecR} {s : NodeR} {l n nF : ℕ}
    (h : bIf(Nat.beq n 18, true, bIf(bAnd(Nat.beq n 36, bAnd(Nat.beq s.mask sp.1,
      bAnd(Nat.beq nF 2, bIf(factK s l sp.2.1, true, factK s l sp.2.2.1)))), true,
      bIf(bAnd(Nat.beq n 120, bAnd(Nat.beq s.mask sp.2.2.2.1, s120K s l sp.2.2.2.2)), true,
      bIf(bAnd(Nat.beq n 360, Nat.beq nF 4), true,
        bAnd(Nat.beq n 720, bAnd(Nat.beq nF 8, s720K s l)))))) = true) :
    n = 18 ∨ (n = 36 ∧ s.mask = sp.1 ∧ nF = 2 ∧
      (factK s l sp.2.1 = true ∨ factK s l sp.2.2.1 = true)) ∨
      (n = 120 ∧ s.mask = sp.2.2.2.1 ∧ s120K s l sp.2.2.2.2 = true) ∨ (n = 360 ∧ nF = 4) ∨
      (n = 720 ∧ nF = 8 ∧ s720K s l = true) := by
  rcases bOr_true h with h | h
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  rcases bOr_true h with h | h
  · obtain ⟨a1, h⟩ := bAnd_true h
    obtain ⟨a2, h⟩ := bAnd_true h
    obtain ⟨a3, a4⟩ := bAnd_true h
    exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2,
      Nat.eq_of_beq_eq_true a3, bOr_true a4⟩)
  rcases bOr_true h with h | h
  · obtain ⟨a1, h⟩ := bAnd_true h
    obtain ⟨a2, a3⟩ := bAnd_true h
    exact Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2, a3⟩))
  rcases bOr_true h with h | h
  · obtain ⟨a1, a2⟩ := bAnd_true h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2⟩)))
  · obtain ⟨a1, h⟩ := bAnd_true h
    obtain ⟨a2, a3⟩ := bAnd_true h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true a1, Nat.eq_of_beq_eq_true a2,
      a3⟩)))

theorem allMems_spec {s : NodeR} {g : ℕ → Bool} (h : allMems s.tree g = true) :
    ∀ c ∈ s.els, g c = true := by
  obtain ⟨h1, h2⟩ := bAnd_true h
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    have h' : g (Nat.land (Nat.shiftRight e 0) 65535) = true :=
      bRec_mem (f := fun e => g (Nat.land (Nat.shiftRight e 0) 65535)) h2 e he
    rw [fld16] at h'
    exact h'

theorem factK_spec {s : NodeR} {l X : ℕ} (h : factK s l X = true) {c : ℕ} (hc : c ∈ s.els) :
    (fixK c l = true → memP X c = true) ∧
      (stabK c l = true → fixK c l = false → memP X c = true → ord3K c = false) := by
  have hg := allMems_spec h c hc
  revert hg
  generalize fixK c l = a1
  generalize memP X c = a2
  generalize stabK c l = a3
  generalize ord3K c = a4
  revert a1 a2 a3 a4
  decide

theorem s120K_spec {s : NodeR} {l m60 : ℕ} (h : s120K s l m60 = true) {c : ℕ} (hc : c ∈ s.els) :
    (fixK c l = true → memP m60 c = true) ∧ (stabK c l = true → fixK c l = false →
      invlK c = true → Nat.beq (centCnt (fixList s l) c) 2 = true) := by
  simp only [s120K] at h
  have hg := allMems_spec h c hc
  revert hg
  generalize fixK c l = a1
  generalize memP m60 c = a2
  generalize stabK c l = a3
  generalize invlK c = a4
  generalize Nat.beq (centCnt (fixList s l) c) 2 = a5
  revert a1 a2 a3 a4 a5
  decide

theorem s720K_spec {s : NodeR} {l : ℕ} (h : s720K s l = true) {c : ℕ} (hc : c ∈ s.els) :
    fixK c l = true ∨ ncAny (fixList s l) c = true := by
  simp only [s720K] at h
  exact bOr_true (allMems_spec h c hc)

theorem ncAny_spec {y : ℕ} : ∀ {F : List ℕ}, ncAny F y = true → ∃ f ∈ F, commK f y = false
  | [], h => absurd h Bool.false_ne_true
  | f :: F, h => by
    have e : ncAny (f :: F) y =
        Bool.rec (motive := fun _ => Bool) true (ncAny F y) (commK f y) := rfl
    rw [e] at h
    cases hc : commK f y
    · exact ⟨f, List.mem_cons.mpr (Or.inl rfl), hc⟩
    · rw [hc] at h
      obtain ⟨g, hg, h'⟩ := ncAny_spec h
      exact ⟨g, List.mem_cons.mpr (Or.inr hg), h'⟩

theorem centCnt_eq (x : ℕ) : ∀ F : List ℕ, centCnt F x = F.countP fun f => commK f x
  | [] => rfl
  | f :: F => by
    have e : centCnt (f :: F) x = Bool.rec (motive := fun _ => ℕ) 0 1 (commK f x) + centCnt F x :=
      rfl
    rw [e, nIf_eq, centCnt_eq x F, List.countP_cons, Nat.add_comm]

theorem fixList_eq (s : NodeR) (l : ℕ) : fixList s l =
    (s.tree.map (· % 65536)).filter (fun c => fixK c l) ++
      Bool.rec (motive := fun _ => List ℕ) [] [33825] (fixK 33825 l) := by
  have key : ∀ tr : List ℕ, List.rec (motive := fun _ => List ℕ)
      (Bool.rec (motive := fun _ => List ℕ) [] [oneP] (fixK oneP l))
      (fun e _ ih => Bool.rec (motive := fun _ => List ℕ) ih
        (Nat.land (Nat.shiftRight e 0) 65535 :: ih) (fixK (Nat.land (Nat.shiftRight e 0) 65535) l))
      tr = (tr.map (· % 65536)).filter (fun c => fixK c l) ++
        Bool.rec (motive := fun _ => List ℕ) [] [33825] (fixK 33825 l) := by
    intro tr
    induction tr with
    | nil => rfl
    | cons e t ih =>
      dsimp only
      rw [fld16, ih, List.map_cons, List.filter_cons]
      cases fixK (e % 65536) l <;> rfl
  exact key s.tree

theorem fixList_perm (s : NodeR) (l : ℕ) :
    (fixList s l).Perm (s.els.filter fun c => fixK c l) := by
  rw [fixList_eq, NodeR.els, List.filter_cons]
  cases fixK 33825 l
  · exact List.Perm.of_eq (List.append_nil _)
  · exact List.perm_append_singleton _ _

theorem lineK_sound {spM : ℕ} {L : List NodeR} {sp : SpecR} {lines : List ℕ} {S : Spec}
    (he : elemsOK spM = true) (hL : ovK spM L = true) (hl : linesOK lines = true)
    (hS : (S.s36.2, S.a36.2, S.b36.2, S.s120.2, S.m60) = sp) (h : lineK sp L lines = true) :
    lineOk S (L.map toNode) = true := by
  subst hS
  unfold lineOk
  rw [List.all_eq_true]
  intro s hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
  have hF : ∀ l ∈ lines, lineOneK (S.s36.2, S.a36.2, S.b36.2, S.s120.2, S.m60) s0 l = true :=
    bRec_mem (bRec_mem h s0 hs0)
  have hnk : nodeK spM L s0 = true := bRec_mem (f := nodeK spM L) hL s0 hs0
  obtain ⟨h1, -, -, h4, -, -⟩ := nodeK_parts hnk
  obtain ⟨-, hnd, hlt, -⟩ := tree_facts h1 h4
  have hsy := (nodeK_sound he hL hs0).2.2.1
  have hels : (toNode s0).els = s0.els.map dec := rfl
  have h0 : 0 ∉ s0.els := fun h0 =>
    absurd (hsy (dec 0) (List.mem_map_of_mem (f := dec) h0)) (by decide)
  have hlen : s0.els.length < 65536 := by
    have hsub : s0.els ⊆ List.range' 1 65535 := fun c hc => by
      have h1 := hlt c hc
      have h2 : c ≠ 0 := fun h => h0 (by rw [← h]; exact hc)
      rw [List.mem_range'_1]
      omega
    have := (hnd.subperm hsub).length_le
    rw [List.length_range'] at this
    omega
  rw [List.all_eq_true]
  intro l hl'
  apply imp_bool
  intro hfe
  obtain ⟨u, hu, v, hv, h0u, h0v, huv, hbj, rfl⟩ := mem_tiLinesC hl'
  obtain ⟨L0, hL0, hiL⟩ := lines_spec hl hu hv h0u h0v huv hbj
  have hone := hF L0 hL0
  have hst := stab_eq hu hv h0u h0v huv hiL
  have hfx := fix_eq hu hv h0u h0v huv hiL
  have hfs : ∀ c, fixK c L0 = true → stabK c L0 = true := by
    intro c hc
    rw [hfx c, List.all_eq_true] at hc
    rw [hst c, List.all_eq_true]
    intro y hy
    rw [beq_iff_eq.mp (hc y hy)]
    exact List.contains_iff_mem.mpr hy
  have hNl : nrmL (s0.els.map dec) [u, v, u ^^^ v] =
      (s0.els.filter fun c => stabK c L0).map dec := by
    rw [nrmL, List.filter_map]
    congr 1
    exact List.filter_congr fun c _ => (hst c).symm
  have hFl : fixL (s0.els.map dec) [u, v, u ^^^ v] =
      (s0.els.filter fun c => fixK c L0).map dec := by
    rw [fixL, List.filter_map]
    congr 1
    exact List.filter_congr fun c _ => (hfx c).symm
  have hsf : (s0.els.countP fun x => stabK x L0 && fixK x L0) =
      s0.els.countP fun x => fixK x L0 := by
    apply List.countP_congr
    intro c _
    cases hf : fixK c L0
    · simp
    · simp [hfs c hf]
  have hb1 : (s0.els.countP fun x => stabK x L0) < 65536 :=
    lt_of_le_of_lt List.countP_le_length hlen
  have hb2 : (s0.els.countP fun x => stabK x L0 && fixK x L0) < 65536 :=
    lt_of_le_of_lt List.countP_le_length hlen
  obtain ⟨f0, f16, f32, f48, f49⟩ := cntE_fld
    (d := s0.els.any fun x => stabK x L0 && !fixK x L0 && ord3K x)
    (e := s0.els.any fun x => stabK x L0 && !fixK x L0 && invlK x) hb1 hb2 hlen
  rw [← cntK_eq L0 hlen] at f0 f16 f32 f48 f49
  simp only [feasible, hels, hNl, List.length_map, ← List.countP_eq_length_filter,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfe
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hfe
  have hd3 : (s0.els.any fun x => stabK x L0 && !fixK x L0 && ord3K x) = true := by
    obtain ⟨y, hy, hy'⟩ := List.any_eq_true.mp hB
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
    refine List.any_eq_true.mpr ⟨c, hc1, ?_⟩
    rw [isNT_eq, ← hfx c, ← ord3K_eq (hlt c hc1), Bool.and_eq_true] at hy'
    rw [hc2, hy'.1, hy'.2]
    rfl
  have hd2 : (s0.els.any fun x => stabK x L0 && !fixK x L0 && invlK x) = true := by
    obtain ⟨y, hy, hy'⟩ := List.any_eq_true.mp hD
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
    refine List.any_eq_true.mpr ⟨c, hc1, ?_⟩
    rw [isNT_eq, ← hfx c, ← invlK_eq (hlt c hc1), Bool.and_eq_true] at hy'
    rw [hc2, hy'.1, hy'.2]
    rfl
  have hfeas : feasK (cntK s0 L0) = true := by
    apply feasK_intro
    · rw [f0, f32]
      exact hA
    · rw [f48, hd3]
      rfl
    · rw [f0, f32]
      exact hC
    · rw [f49, hd2]
      rfl
  have hcon := bIf_true hone hfeas
  have hfac : ∀ X, factK s0 L0 X = true →
      ((s0.els.filter fun c => fixK c L0).map dec).all (memM X) = true ∧
      ((s0.els.filter fun c => stabK c L0).map dec).all
        (fun x => !(memM X x && ord3 x && isNT x [u, v, u ^^^ v])) = true := by
    intro X hX
    constructor
    · rw [List.all_eq_true]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
      rw [memM_dec X (hlt c hc1)]
      exact (factK_spec hX hc1).1 hc2
    · rw [List.all_eq_true]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
      have key := (factK_spec hX hc1).2 hc2
      rw [memM_dec X (hlt c hc1), ← ord3K_eq (hlt c hc1), isNT_eq, ← hfx c]
      revert key
      cases memP X c <;> cases ord3K c <;> cases fixK c L0 <;> decide
  have hcc : ∀ c, centCnt (fixList s0 L0) c = ((s0.els.filter fun c => fixK c L0).map dec).countP
      fun f => mulC f (dec c) == mulC (dec c) f := by
    intro c
    rw [centCnt_eq, List.Perm.countP_eq _ (fixList_perm s0 L0), List.countP_map]
    apply List.countP_congr
    intro f _
    rw [commK_eq]
    rfl
  simp only [concl, hels, hNl, hFl, List.length_map, ← List.countP_eq_length_filter,
    Bool.or_eq_true]
  rcases conclF_cases (n := Nat.land (Nat.shiftRight (cntK s0 L0) 32) 65535)
    (nF := Nat.land (Nat.shiftRight (cntK s0 L0) 16) 65535) hcon with
    hn | ⟨hn, hm, h2, hX⟩ | ⟨hn, hm, hs1⟩ | ⟨hn, h4⟩ | ⟨hn, h8, hs7⟩
  · rw [f32] at hn
    exact Or.inl (Or.inl (Or.inl (Or.inl (beq_iff_eq.mpr hn))))
  · rw [f32] at hn
    rw [f16, hsf] at h2
    refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    rcases hX with hX | hX
    · exact ⟨⟨⟨hn, hm⟩, h2⟩, Or.inl (hfac _ hX)⟩
    · exact ⟨⟨⟨hn, hm⟩, h2⟩, Or.inr (hfac _ hX)⟩
  · rw [f32] at hn
    refine Or.inl (Or.inl (Or.inr ?_))
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨hn, hm⟩, ?_⟩, ?_⟩
    · rw [List.all_eq_true]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
      rw [memM_dec _ (hlt c hc1)]
      exact (s120K_spec hs1 hc1).1 hc2
    · rw [List.all_eq_true]
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      obtain ⟨hc1, hc2⟩ := List.mem_filter.mp hc
      have key := (s120K_spec hs1 hc1).2 hc2
      rw [hcc c] at key
      rw [← invlK_eq (hlt c hc1), isNT_eq, ← hfx c]
      revert key
      generalize (((s0.els.filter fun c => fixK c L0).map dec).countP
        fun f => mulC f (dec c) == mulC (dec c) f) = k
      cases invlK c <;> cases fixK c L0 <;> simp
  · rw [f32] at hn
    rw [f16, hsf] at h4
    refine Or.inl (Or.inr ?_)
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hn, h4⟩
  · rw [f32] at hn
    rw [f16, hsf] at h8
    refine Or.inr ?_
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨hn, h8⟩, ?_⟩
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨c, hc1, rfl⟩ := List.mem_map.mp hy
    rcases s720K_spec hs7 hc1 with hf | hnc
    · have hmem : dec c ∈ (s0.els.filter fun c => fixK c L0).map dec :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hc1, hf⟩)
      rw [Bool.or_eq_true]
      exact Or.inr (List.contains_iff_mem.mpr hmem)
    · obtain ⟨f, hf1, hf2⟩ := ncAny_spec hnc
      have hf3 := (fixList_perm s0 L0).subset hf1
      cases hA : (((s0.els.filter fun c => fixK c L0).map dec).all
        fun f' => mulC f' (dec c) == mulC (dec c) f')
      · rfl
      · have := List.all_eq_true.mp hA (dec f) (List.mem_map_of_mem hf3)
        rw [← commK_eq, hf2] at this
        exact absurd this Bool.false_ne_true

theorem quadK_sound {spM : ℕ} {L : List NodeR} {sp : SpecR} {lines : List ℕ} {S : Spec}
    (he : elemsOK spM = true) (hL : ovK spM L = true) (hl : linesOK lines = true)
    (hS : (S.s36.2, S.a36.2, S.b36.2, S.s120.2, S.m60) = sp) (h : quadK sp L lines = true) :
    quadOk S (L.map toNode) = true := by
  unfold quadOk
  rw [List.all_eq_true]
  intro s hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
  have hF := bRec_mem h s0 hs0
  apply imp_bool
  intro hc
  have hc' : Bool.rec (motive := fun _ => Bool) (Nat.ble 360 (sizeK s0)) true
      (Nat.beq s0.mask sp.2.2.2.1) = true := by
    apply bOr_intro
    rw [Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · left
      have hm : s0.mask = S.s120.2 := beq_iff_eq.mp hc
      rw [hm, ← hS]
      exact Nat.beq_refl _
    · right
      rw [sizeK_eq]
      apply Nat.ble_eq_true_of_le
      simpa [toNode] using of_decide_eq_true hc
  have hA := all16_spec (bIf_true hF hc')
  rw [List.all_eq_true]
  intro a ha
  rw [List.mem_range] at ha
  have hA' := hA a ha
  rw [List.all_eq_true]
  intro l hlt
  apply imp_bool
  intro hz
  obtain ⟨u, hu, v, hv, h0u, h0v, huv, hbj, rfl⟩ := mem_tiLinesC hlt
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.not_eq_true'] at hz
  obtain ⟨hqu, hqv, hqw⟩ := hz
  obtain ⟨L0, hL0, hiL⟩ := lines_spec hl hu hv h0u h0v huv hbj
  have hz0 := qZero_true ha hu hv h0u h0v huv hiL hqu hqv hqw
  have hmv := bIf_true hA' (anyRec_intro hL0 hz0)
  obtain ⟨c, hc, hcv⟩ := anyMems_spec hmv
  obtain ⟨w, hw, hne⟩ := any16_spec hcv
  have hne' := bNot_true hne
  rw [List.any_eq_true]
  refine ⟨dec c, List.mem_map_of_mem hc, ?_⟩
  rw [List.any_eq_true]
  refine ⟨w, List.mem_range.mpr hw, ?_⟩
  rw [← mv_eq]
  have hq1 := qK_eq a ha (mv c w) (mv_lt _ _)
  have hq2 := qK_eq a ha w hw
  rw [hq1, hq2] at hne'
  revert hne'
  cases qJ a (mv c w) <;> cases qJ a w <;> decide

section SpecialK

open CFSG.Quasithin

@[expose] def spkE (w : ℕ × ℕ) : ℕ := w.1 + 4 * w.2

@[expose] def spkD (a : ℕ) : ℕ × ℕ := (a % 4, a / 4 % 4)

@[expose] def spkF (c1 c2 w : ℕ × ℕ) : ℕ × ℕ :=
  (f4m c1.1 w.1 ^^^ f4m c2.1 w.2, f4m c1.2 w.1 ^^^ f4m c2.2 w.2)

@[expose] def spkW (k : ℕ) (w : ℕ × ℕ) : ℕ × ℕ := if k == 0 then w else (frobC w.1, frobC w.2)

@[expose] noncomputable def spkPar (g : ℕ → ℕ) : ℕ :=
  Nat.land (Nat.rec (motive := fun _ => Nat) 0 (fun j ih => Nat.add ih
    (Nat.rec (motive := fun _ => Nat) 0 (fun i ih2 => Nat.add ih2
      (nIf(Nat.blt (g j) (g i), 1, 0))) j)) 5) 1

@[expose] noncomputable def spkChain (g : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih (Nat.shiftLeft (g i) (Nat.mul 3 i))) 5

@[expose] noncomputable def spkOr (g : ℕ → ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i ih => Nat.lor ih (Nat.shiftLeft 1 (g i))) 5

theorem spk_psiK : ∀ x < 16, psiK x = spkE (psiC x) := by decide +kernel

theorem spk_psiC_lt : ∀ x < 16, (psiC x).1 < 4 ∧ (psiC x).2 < 4 := by decide +kernel

theorem spk_psiK_inj : ∀ x < 16, ∀ y < 16, psiK x = psiK y → x = y := by decide +kernel

theorem spk_psiInv : ∀ w < 16, psiInv (spkD w) < 16 ∧ psiK (psiInv (spkD w)) = w := by
  decide +kernel

theorem spk_matK : ∀ a < 16, ∀ b < 16, ∀ w < 16, matK a b w =
    spkE (spkF (spkD a) (spkD b) (spkD w)) := by decide +kernel

theorem spk_frobK : ∀ w < 16, frobK w = spkE (frobC (spkD w).1, frobC (spkD w).2) := by
  decide +kernel

theorem spk_det : ∀ a < 16, ∀ b < 16,
    Nat.xor (f4mK fld(a, 0, 3) fld(b, 2, 3)) (f4mK fld(b, 0, 3) fld(a, 2, 3)) =
      (f4m (spkD a).1 (spkD b).2 ^^^ f4m (spkD b).1 (spkD a).2) := by decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
theorem spk_nz : ∀ a < 16, ∀ b < 16, ∀ w < 16, ∀ k < 2,
    (f4m (spkD a).1 (spkD b).2 ^^^ f4m (spkD b).1 (spkD a).2) = 1 →
    spkF (spkD a) (spkD b) (spkW k (spkD w)) = (0, 0) → w = 0 := by decide +kernel

theorem spk_ptK : ∀ w < 16, (Nat.rec (motive := fun _ => Nat) 0 (fun i ih =>
        (fun j => nIf(bIf(Nat.beq (smulK 1 (ptCode j)) w, true, bIf(Nat.beq (smulK 2 (ptCode j)) w,
          true, Nat.beq (smulK 3 (ptCode j)) w)), j, ih)) (Nat.sub 4 i)) 5 : ℕ) =
      ptIdx (spkD w) := by decide +kernel

theorem spk_pts : ∀ i < 5, ptCode i < 16 ∧ 0 < ptCode i ∧ spkD (ptCode i) = pts.getD i (0, 0) ∧
    ptIdx (spkD (ptCode i)) = i := by decide +kernel

@[expose] noncomputable def spkPackB (p a0 a1 a2 a3 a4 : ℕ) : Bool :=
  bAnd(Nat.beq (appP p 0) a0, bAnd(Nat.beq (appP p 1) a1, bAnd(Nat.beq (appP p 2) a2,
    bAnd(Nat.beq (appP p 3) a3, bAnd(Nat.beq (appP p 4) a4,
      bIf(bAnd(Nat.beq a0 0, bAnd(Nat.beq a1 1, bAnd(Nat.beq a2 2, bAnd(Nat.beq a3 3,
        Nat.beq a4 4)))), Nat.beq p idP, true))))))

theorem spk_pack : ∀ a0 < 8, ∀ a1 < 8, ∀ a2 < 8, ∀ a3 < 8, ∀ a4 < 8,
    spkPackB (spkChain fun i => [a0, a1, a2, a3, a4].getD i 0) a0 a1 a2 a3 a4 = true := by
  decide +kernel

@[expose] noncomputable def spkPermB (l : List ℕ) : Bool :=
  bIf(Nat.beq (spkOr fun i => l.getD i 0) 31,
    bAnd(decide (PermCond l), bAnd(l.all (· < 5) && decide l.Nodup,
      bAnd(bIf(decide (∀ i, permOfList l i = i), decide (l = [0, 1, 2, 3, 4]), true),
        bIf(Nat.beq (spkPar fun i => l.getD i 0) 0, decide (Equiv.Perm.sign (permOfList l) = 1),
          true)))), true)

theorem spk_perm5 : ∀ a0 < 8, ∀ a1 < 8, ∀ a2 < 8, ∀ a3 < 8, ∀ a4 < 8,
    spkPermB [a0, a1, a2, a3, a4] = true := by
  decide +kernel

theorem spk_psiK_lt : ∀ x < 16, psiK x < 16 := by decide +kernel

theorem spk_frobK_lt : ∀ w < 16, frobK w < 16 := by decide +kernel

theorem spk_psiInv_psiK : ∀ x < 16, psiInv (spkD (psiK x)) = x := by decide +kernel

theorem spk_pk3 : ∀ a < 16, ∀ b < 16,
    bAnd(Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 0, 0, 15) a,
      bAnd(Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 0, 4, 15) b,
      bAnd(Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 0, 8, 1) 0,
      bAnd(Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 256, 0, 15) a,
      bAnd(Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 256, 4, 15) b,
        Nat.beq fld(Nat.lor (Nat.lor a (Nat.shiftLeft b 4)) 256, 8, 1) 1))))) = true := by
  decide +kernel

theorem spk_f4c_xor : ∀ x < 4, ∀ y < 4, f4c (x ^^^ y) = f4c x + f4c y := by decide +kernel

theorem spk_f4c_mul : ∀ x < 4, ∀ y < 4, f4c (f4m x y) = f4c x * f4c y := by decide +kernel

theorem spk_f4c_frob : ∀ x < 4, f4c (frobC x) = RuType.frobF4 (f4c x) := by decide +kernel

theorem spk_detF : ∀ a < 4, ∀ b < 4, ∀ c < 4, ∀ d < 4, (f4m a d ^^^ f4m c b) = 1 →
    f4c a * f4c d - f4c c * f4c b = 1 := by decide +kernel

theorem spk_right : ∀ k < 2, (Multiplicative.ofAdd ((k : ℕ) : ZMod 2) = 1 ↔ k = 0) := by
  decide +kernel

theorem spk_f4m_lt (x y : ℕ) : f4m x y < 4 := by
  dsimp only [f4m]
  omega

theorem spk_frobC_lt (x : ℕ) : frobC x < 4 := spk_f4m_lt x x

theorem spk_xor_lt {x y : ℕ} (hx : x < 4) (hy : y < 4) : x ^^^ y < 4 :=
  Nat.xor_lt_two_pow (n := 2) hx hy

theorem spk_F_lt (c1 c2 w : ℕ × ℕ) : (spkF c1 c2 w).1 < 4 ∧ (spkF c1 c2 w).2 < 4 :=
  ⟨spk_xor_lt (spk_f4m_lt _ _) (spk_f4m_lt _ _), spk_xor_lt (spk_f4m_lt _ _) (spk_f4m_lt _ _)⟩

theorem spk_DE {p : ℕ × ℕ} (hp : p.1 < 4 ∧ p.2 < 4) : spkD (spkE p) = p := by
  obtain ⟨p1, p2⟩ := p
  simp only [spkD, spkE] at *
  ext <;> simp <;> omega

theorem spk_nbeq (x y : ℕ) : Nat.beq x y = (x == y) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq]

theorem spk_nb {x y : ℕ} (h : Nat.beq x y = true) : (x == y) = true := by
  rw [← spk_nbeq]
  exact h

theorem spk_beqE {p q : ℕ × ℕ} (hp : p.1 < 4 ∧ p.2 < 4) (hq : q.1 < 4 ∧ q.2 < 4) :
    Nat.beq (spkE p) (spkE q) = (p == q) := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only [spkE] at *
  rw [Bool.eq_iff_iff, Nat.beq_eq, beq_iff_eq, Prod.mk.injEq]
  omega

theorem spk_cmp {y a b w : ℕ} (hy : y < 16) (ha : a < 16) (hb : b < 16) (hw : w < 16) :
    Nat.beq (psiK y) (matK a b w) = (psiC y == spkF (spkD a) (spkD b) (spkD w)) := by
  rw [spk_psiK y hy, spk_matK a ha b hb w hw]
  exact spk_beqE (spk_psiC_lt y hy) (spk_F_lt _ _ _)

theorem spk_v {a b y v k : ℕ} (ha : a < 16) (hb : b < 16) (hy : y < 16) (hv : v < 16)
    (hk : k < 2) :
    Nat.beq (psiK y) (matK a b (Bool.rec (motive := fun _ => ℕ) (frobK (psiK v)) (psiK v)
      (Nat.beq k 0))) = (psiC y == spkF (spkD a) (spkD b) (spkW k (psiC v))) := by
  have hv' := spk_psiK_lt v hv
  interval_cases k
  · change Nat.beq (psiK y) (matK a b (psiK v)) = (psiC y == spkF (spkD a) (spkD b) (psiC v))
    rw [spk_cmp hy ha hb hv', spk_psiK v hv, spk_DE (spk_psiC_lt v hv)]
  · change Nat.beq (psiK y) (matK a b (frobK (psiK v))) =
      (psiC y == spkF (spkD a) (spkD b) (frobC (psiC v).1, frobC (psiC v).2))
    rw [spk_cmp hy ha hb (spk_frobK_lt _ hv'), spk_frobK _ hv', spk_psiK v hv,
      spk_DE (spk_psiC_lt v hv), spk_DE ⟨spk_frobC_lt _, spk_frobC_lt _⟩]

theorem spk_natAll_intro {f : ℕ → Bool} : ∀ n, (∀ a < n, f a = true) →
    Nat.rec (motive := fun _ => Bool) true
      (fun a ih => Bool.rec (motive := fun _ => Bool) false ih (f a)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    have h1 := h n (by omega)
    have h2 := spk_natAll_intro n fun a ha => h a (by omega)
    change Bool.rec (motive := fun _ => Bool) false _ (f n) = true
    rw [h1]
    exact h2

theorem spk_allV_eq {f g : ℕ → Bool} (h : ∀ v < 16, f v = g v) :
    allV f = (List.range 16).all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true]
  simp only [List.mem_range]
  constructor
  · intro hf v hv
    rw [← h v hv]
    exact all16_spec hf v hv
  · intro hg
    exact spk_natAll_intro 16 fun v hv => (h v hv).trans (hg v hv)

theorem spk_allL {l : List ℕ} {f : ℕ → Bool} (h : allL l f = true) : ∀ x ∈ l, f x = true :=
  bRec_mem h

theorem spk_anyL {l : List ℕ} {f : ℕ → Bool} (h : anyL l f = true) : ∃ x ∈ l, f x = true :=
  anyRec_mem h

theorem spk_incL : ∀ (l : List ℕ) (b : ℕ), List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih b => bAnd(Nat.ble b x, bAnd(Nat.blt x 65536, ih (Nat.succ x)))) l b = true →
    (∀ x ∈ l, b ≤ x ∧ x < 65536) ∧ l.Pairwise (· < ·)
  | [], _, _ => ⟨fun _ hx => by simp at hx, List.Pairwise.nil⟩
  | x :: t, b, h => by
    obtain ⟨h1, h⟩ := bAnd_true h
    obtain ⟨h2, h3⟩ := bAnd_true h
    obtain ⟨ih1, ih2⟩ := spk_incL t (x + 1) h3
    have hb : b ≤ x := Nat.le_of_ble_eq_true h1
    have hx : x < 65536 := by simpa [Nat.blt_eq] using h2
    refine ⟨fun y hy => ?_, List.Pairwise.cons (fun y hy => by have := ih1 y hy; omega) ih2⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨hb, hx⟩
    · have := ih1 y hy
      omega

theorem spk_inc {l : List ℕ} (h : incL l = true) : (∀ x ∈ l, x < 65536) ∧ l.Nodup :=
  have hl := spk_incL l 0 h
  ⟨fun x hx => (hl.1 x hx).2, hl.2.imp fun h => Nat.ne_of_lt h⟩

theorem spk_nodup_map {l : List ℕ} (h : incL l = true) : (l.map dec).Nodup :=
  (spk_inc h).2.map_on fun x hx y hy hxy => dec_inj ((spk_inc h).1 x hx) ((spk_inc h).1 y hy) hxy

theorem spk_maskL_rec : ∀ (l : List ℕ) (m c : ℕ), (List.rec (motive := fun _ => ℕ → ℕ)
    (fun m => m) (fun x _ ih m => CFSG.KC.Loop.strictN (Nat.lor m (Nat.shiftLeft 1 x)) ih)
      l m).testBit c = true ↔ m.testBit c = true ∨ c ∈ l
  | [], m, c => by simp
  | x :: t, m, c => by
    change (CFSG.KC.Loop.strictN (Nat.lor m (Nat.shiftLeft 1 x)) _).testBit c = true ↔ _
    rw [strictN_eq, spk_maskL_rec t]
    change (m ||| 1 <<< x).testBit c = true ∨ c ∈ t ↔ _
    rw [Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    rw [@eq_comm _ x c]
    exact or_assoc

theorem spk_maskL {l : List ℕ} {c : ℕ} : (maskL l).testBit c = true ↔ c ∈ l :=
  (spk_maskL_rec l 0 c).trans (by simp)

theorem spk_maskOf {l : List ℕ} (hl : ∀ x ∈ l, x < 65536) : maskOf (l.map dec) = maskL l := by
  apply Nat.eq_of_testBit_eq
  intro c
  rw [Bool.eq_iff_iff, maskOf, testBit_foldl_addM, spk_maskL]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or, List.mem_map,
    exists_exists_and_eq_and]
  constructor
  · rintro ⟨x, hx, hxc⟩
    rw [codeC_dec (hl x hx)] at hxc
    exact hxc ▸ hx
  · intro hc
    exact ⟨c, hc, codeC_dec (hl c hc)⟩

theorem spk_memM {m x : ℕ} (hx : x < 65536) : memM m (dec x) = memP m x := by
  rw [memM, codeC_dec hx, memP_eq]

theorem spk_cntL (l : List ℕ) (f : ℕ → Bool) : cntL l f = (l.filter f).length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    have e : cntL (x :: t) f = Nat.add (Bool.rec (motive := fun _ => ℕ) 0 1 (f x)) (cntL t f) :=
      rfl
    rw [e, ih, List.filter_cons]
    cases f x <;> simp <;> omega

theorem spk_lenL (l : List ℕ) : lenL l = l.length := by
  rw [lenL, spk_cntL, List.filter_true]

theorem spk_filterRec (l : List ℕ) (f : ℕ → Bool) : List.rec (motive := fun _ => List ℕ) []
    (fun x _ ih => Bool.rec (motive := fun _ => List ℕ) ih (x :: ih) (f x)) l = l.filter f := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    change Bool.rec (motive := fun _ => List ℕ) _ (x :: _) (f x) = _
    rw [List.filter_cons, ← ih]
    cases f x <;> rfl

theorem spk_all2 : ∀ (l q : List ℕ) (f : ℕ → ℕ → Bool), all2 l q f = true →
    l.length = q.length ∧ ∀ x p, (x, p) ∈ l.zip q → f x p = true
  | [], [], _, _ => ⟨rfl, by simp⟩
  | [], _ :: _, _, h => absurd h Bool.false_ne_true
  | _ :: _, [], _, h => absurd h Bool.false_ne_true
  | x :: l, p :: q, f, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    obtain ⟨ih1, ih2⟩ := spk_all2 l q f h2
    refine ⟨by simp [ih1], fun y r hyr => ?_⟩
    rw [List.zip_cons_cons, List.mem_cons] at hyr
    rcases hyr with hyr | hyr
    · simp only [Prod.mk.injEq] at hyr
      obtain ⟨rfl, rfl⟩ := hyr
      exact h1
    · exact ih2 y r hyr

theorem spk_zip_left : ∀ (l q : List ℕ), l.length = q.length → ∀ x ∈ l, ∃ p, (x, p) ∈ l.zip q
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp at h
  | x :: l, p :: q, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨p, by simp⟩
    · obtain ⟨r, hr⟩ := spk_zip_left l q (by simpa using h) y hy
      exact ⟨r, by simp [hr]⟩

theorem spk_all_map {l : List ℕ} {g : List ℕ → Bool} (h : ∀ x ∈ l, g (dec x) = true) :
    (l.map dec).all g = true :=
  List.all_eq_true.mpr fun y hy => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact h x hx

theorem spk_any_map {l : List ℕ} {g : List ℕ → Bool} {x : ℕ} (hx : x ∈ l) (h : g (dec x) = true) :
    (l.map dec).any g = true :=
  List.any_eq_true.mpr ⟨dec x, List.mem_map_of_mem hx, h⟩

theorem spk_contains_map {l : List ℕ} {x : ℕ} (hx : x ∈ l) : (l.map dec).contains (dec x) = true :=
  List.elem_eq_true_of_mem (List.mem_map_of_mem hx)

theorem spk_imp {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true) :
    (!c || t) = true := by
  cases c
  · rfl
  · exact h

theorem spk_oneP_lt : oneP < 65536 := by decide

theorem spk_beq_dec {a b : ℕ} (ha : a < 65536) (hb : b < 65536) :
    (dec a == dec b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  exact ⟨dec_inj ha hb, congrArg dec⟩

theorem spk_commK (x y : ℕ) : commK x y = (mulC (dec x) (dec y) == mulC (dec y) (dec x)) := by
  rw [← dec_mulP, ← dec_mulP, spk_beq_dec (mulP_lt _ _) (mulP_lt _ _)]
  rfl

theorem spk_ord3 {x : ℕ} (hx : x < 65536) : ord3 (dec x) = ord3K x := by
  rw [ord3, ← dec_oneP, ← dec_mulP, ← dec_mulP, bne, spk_beq_dec hx spk_oneP_lt,
    spk_beq_dec (mulP_lt _ _) spk_oneP_lt]
  unfold ord3K
  cases Nat.beq x oneP <;> rfl

theorem spk_powK (x : ℕ) : ∀ n, dec (powK x n) = powC (dec x) n
  | 0 => dec_oneP
  | n + 1 => by
    change dec (mulP (powK x n) x) = mulC (powC (dec x) n) (dec x)
    rw [dec_mulP, spk_powK x n]

theorem spk_powK_lt (x : ℕ) : ∀ n, powK x n < 65536
  | 0 => spk_oneP_lt
  | n + 1 => mulP_lt _ _

theorem spk_mv_mul (d e v : ℕ) : mv (mulP d e) v = mv d (mv e v) := by
  rw [mv_eq, mv_eq, mv_eq, dec_mulP]
  have hd := validC4_dec d
  have he := validC4_dec e
  apply vec4_lt_inj (mulVecC_lt16 (validC4_mulC hd he) v) (mulVecC_lt16 hd _)
  rw [← decodeC4_mulVec (validC4_mulC hd he).1, decodeC4_mulC hd.1 he.1, ← Matrix.mulVec_mulVec,
    decodeC4_mulVec he.1, decodeC4_mulVec hd.1]

theorem spk_validB (x : ℕ) : validB (dec x) = true := by
  have h := validC4_dec x
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
  exact h

theorem spk_appP_lt (p i : ℕ) : appP p i < 8 := Nat.lt_succ_of_le Nat.and_le_right

theorem spk_psiInvK_lt (T w : ℕ) : psiInvK T w < 16 := Nat.lt_succ_of_le Nat.and_le_right

theorem spk_ptK_lt (P w : ℕ) : ptK P w < 8 := Nat.lt_succ_of_le Nat.and_le_right

theorem spk_getD5 (g : ℕ → ℕ) {x : ℕ} (hx : x < 5) : [g 0, g 1, g 2, g 3, g 4].getD x 0 = g x := by
  interval_cases x <;> rfl

theorem spk_tabs {T P : ℕ} (h : tabsOK T P = true) :
    (∀ w < 16, psiInvK T w = psiInv (spkD w)) ∧ (∀ w < 16, ptK P w = ptIdx (spkD w)) := by
  obtain ⟨h1, h2⟩ := bAnd_true h
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have e := Nat.eq_of_beq_eq_true (all16_spec h1 w hw)
    obtain ⟨i1, i2⟩ := spk_psiInv w hw
    exact spk_psiK_inj _ (spk_psiInvK_lt T w) _ i1 (e.trans i2.symm)
  · exact (Nat.eq_of_beq_eq_true (all16_spec h2 w hw)).trans (spk_ptK w hw)

theorem spk_semC_lt (x : ℕ) : ((semC (dec x)).1.1 < 4 ∧ (semC (dec x)).1.2 < 4) ∧
    ((semC (dec x)).2.1.1 < 4 ∧ (semC (dec x)).2.1.2 < 4) ∧ (semC (dec x)).2.2 < 2 := by
  have h1 := spk_psiC_lt _ (mv_lt x (psiInv (1, 0)))
  have h2 := spk_psiC_lt _ (mv_lt x (psiInv (0, 1)))
  rw [mv_eq] at h1 h2
  refine ⟨h1, h2, ?_⟩
  change (if _ then 0 else 1) < 2
  split <;> norm_num

theorem spk_sem {T d : ℕ} (ht : ∀ w < 16, psiInvK T w = psiInv (spkD w)) :
    fld(semK T d, 0, 15) = psiK (mv d (psiInv (1, 0))) ∧
    fld(semK T d, 4, 15) = psiK (mv d (psiInv (0, 1))) ∧
    fld(semK T d, 8, 1) = (semC (dec d)).2.2 ∧
    spkD (psiK (mv d (psiInv (1, 0)))) = (semC (dec d)).1 ∧
    spkD (psiK (mv d (psiInv (0, 1)))) = (semC (dec d)).2.1 := by
  have e1 : psiInvK T 1 = psiInv (1, 0) := ht 1 (by norm_num)
  have e4 : psiInvK T 4 = psiInv (0, 1) := ht 4 (by norm_num)
  have hx1 := mv_lt d (psiInv (1, 0))
  have hx4 := mv_lt d (psiInv (0, 1))
  have ha := spk_psiK_lt _ hx1
  have hb := spk_psiK_lt _ hx4
  have hC1 : spkD (psiK (mv d (psiInv (1, 0)))) = (semC (dec d)).1 := by
    rw [spk_psiK _ hx1, spk_DE (spk_psiC_lt _ hx1), mv_eq]
    rfl
  have hC4 : spkD (psiK (mv d (psiInv (0, 1)))) = (semC (dec d)).2.1 := by
    rw [spk_psiK _ hx4, spk_DE (spk_psiC_lt _ hx4), mv_eq]
    rfl
  have hok : allV (fun v => Nat.beq (psiK (mv d v)) (matK (psiK (mv d (psiInv (1, 0))))
      (psiK (mv d (psiInv (0, 1)))) (psiK v))) = (List.range 16).all (fun v =>
        psiC (mulVecC (dec d) v) == spkF (semC (dec d)).1 (semC (dec d)).2.1 (psiC v)) := by
    apply spk_allV_eq
    intro v hv
    rw [spk_cmp (mv_lt _ _) ha hb (spk_psiK_lt v hv), hC1, hC4, spk_psiK v hv,
      spk_DE (spk_psiC_lt v hv), mv_eq]
  have hk : (semC (dec d)).2.2 = if (List.range 16).all (fun v =>
      psiC (mulVecC (dec d) v) == spkF (semC (dec d)).1 (semC (dec d)).2.1 (psiC v)) then 0
      else 1 := rfl
  have hS : semK T d = Nat.lor (Nat.lor (psiK (mv d (psiInv (1, 0))))
      (Nat.shiftLeft (psiK (mv d (psiInv (0, 1)))) 4)) (Bool.rec (motive := fun _ => ℕ) 256 0
        (allV fun v => Nat.beq (psiK (mv d v)) (matK (psiK (mv d (psiInv (1, 0))))
          (psiK (mv d (psiInv (0, 1)))) (psiK v)))) := by
    unfold semK
    rw [e1, e4]
  have hp := spk_pk3 _ ha _ hb
  obtain ⟨p1, hp⟩ := bAnd_true hp
  obtain ⟨p2, hp⟩ := bAnd_true hp
  obtain ⟨p3, hp⟩ := bAnd_true hp
  obtain ⟨p4, hp⟩ := bAnd_true hp
  obtain ⟨p5, p6⟩ := bAnd_true hp
  rw [hk, ← hok, hS]
  refine ⟨?_, ?_, ?_, hC1, hC4⟩ <;> cases allV _
  · exact Nat.eq_of_beq_eq_true p4
  · exact Nat.eq_of_beq_eq_true p1
  · exact Nat.eq_of_beq_eq_true p5
  · exact Nat.eq_of_beq_eq_true p2
  · exact Nat.eq_of_beq_eq_true p6
  · exact Nat.eq_of_beq_eq_true p3

theorem spk_semOk {T d : ℕ} (ht : ∀ w < 16, psiInvK T w = psiInv (spkD w)) :
    semOkK T d = semOk (dec d) := by
  obtain ⟨f0, f4, f8, hC1, hC4⟩ := spk_sem (d := d) ht
  have ha := spk_psiK_lt _ (mv_lt d (psiInv (1, 0)))
  have hb := spk_psiK_lt _ (mv_lt d (psiInv (0, 1)))
  have hk2 := (spk_semC_lt d).2.2
  have hall : allV (fun v => Nat.beq (psiK (mv d v)) (matK (psiK (mv d (psiInv (1, 0))))
      (psiK (mv d (psiInv (0, 1)))) (Bool.rec (motive := fun _ => ℕ) (frobK (psiK v)) (psiK v)
        (Nat.beq (semC (dec d)).2.2 0)))) = (List.range 16).all (fun v =>
          psiC (mulVecC (dec d) v) == spkF (semC (dec d)).1 (semC (dec d)).2.1
            (spkW (semC (dec d)).2.2 (psiC v))) :=
    spk_allV_eq fun v hv => by rw [spk_v ha hb (mv_lt _ _) hv hk2, hC1, hC4, mv_eq]
  have hdet : Nat.beq (Nat.xor (f4mK fld(psiK (mv d (psiInv (1, 0))), 0, 3)
      fld(psiK (mv d (psiInv (0, 1))), 2, 3)) (f4mK fld(psiK (mv d (psiInv (0, 1))), 0, 3)
        fld(psiK (mv d (psiInv (1, 0))), 2, 3))) 1 =
      ((f4m (semC (dec d)).1.1 (semC (dec d)).2.1.2 ^^^ f4m (semC (dec d)).2.1.1
        (semC (dec d)).1.2) == 1) := by
    rw [spk_det _ ha _ hb, hC1, hC4, spk_nbeq]
  simp only [semOkK]
  rw [f0, f4, f8, hall, hdet]
  rfl

theorem spk_semOk_facts {d : ℕ} (h : semOk (dec d) = true) :
    (∀ v < 16, psiC (mv d v) = spkF (semC (dec d)).1 (semC (dec d)).2.1
      (spkW (semC (dec d)).2.2 (psiC v))) ∧ (matC (dec d)).det = 1 := by
  have h' : ((List.range 16).all (fun v => psiC (mulVecC (dec d) v) ==
      spkF (semC (dec d)).1 (semC (dec d)).2.1 (spkW (semC (dec d)).2.2 (psiC v))) &&
      ((f4m (semC (dec d)).1.1 (semC (dec d)).2.1.2 ^^^ f4m (semC (dec d)).2.1.1
        (semC (dec d)).1.2) == 1)) = true := h
  rw [Bool.and_eq_true, List.all_eq_true] at h'
  obtain ⟨hall, hdet⟩ := h'
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, -⟩ := spk_semC_lt d
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [mv_eq]
    exact beq_iff_eq.mp (hall v (List.mem_range.mpr hv))
  · rw [matC, Matrix.det_fin_two_of]
    exact spk_detF _ a1 _ a2 _ b1 _ b2 (beq_iff_eq.mp hdet)

theorem spk_inj {d : ℕ} (h : semOk (dec d) = true) : ∀ v < 16, mv d v = 0 → v = 0 := by
  intro v hv h0
  obtain ⟨hall, -⟩ := spk_semOk_facts h
  obtain ⟨hc1, hc2, hk⟩ := spk_semC_lt d
  have e := hall v hv
  rw [h0] at e
  have e' : spkF (spkD (spkE (semC (dec d)).1)) (spkD (spkE (semC (dec d)).2.1))
      (spkW (semC (dec d)).2.2 (spkD (psiK v))) = (0, 0) := by
    rw [spk_DE hc1, spk_DE hc2, spk_psiK v hv, spk_DE (spk_psiC_lt v hv), ← e]
    rfl
  have hdet' : (f4m (spkD (spkE (semC (dec d)).1)).1 (spkD (spkE (semC (dec d)).2.1)).2 ^^^
      f4m (spkD (spkE (semC (dec d)).2.1)).1 (spkD (spkE (semC (dec d)).1)).2) = 1 := by
    have h' : ((List.range 16).all (fun v => psiC (mulVecC (dec d) v) ==
        spkF (semC (dec d)).1 (semC (dec d)).2.1 (spkW (semC (dec d)).2.2 (psiC v))) &&
        ((f4m (semC (dec d)).1.1 (semC (dec d)).2.1.2 ^^^ f4m (semC (dec d)).2.1.1
          (semC (dec d)).1.2) == 1)) = true := h
    rw [Bool.and_eq_true] at h'
    rw [spk_DE hc1, spk_DE hc2]
    exact beq_iff_eq.mp h'.2
  have hE1 : spkE (semC (dec d)).1 < 16 := by unfold spkE; omega
  have hE2 : spkE (semC (dec d)).2.1 < 16 := by unfold spkE; omega
  have h0' := spk_nz _ hE1 _ hE2 _ (spk_psiK_lt v hv) _ hk hdet' e'
  exact spk_psiK_inj v hv 0 (by norm_num) (h0'.trans rfl)

theorem spk_sig1 {a1 a2 b1 b2 w1 w2 : ℕ} (ha1 : a1 < 4) (ha2 : a2 < 4) (hb1 : b1 < 4)
    (hb2 : b2 < 4) (hw1 : w1 < 4) (hw2 : w2 < 4) (u : Fin 2 → RuType.F4) (hu0 : u 0 = f4c w1)
    (hu1 : u 1 = f4c w2) :
    (!![f4c a1, f4c b1; f4c a2, f4c b2]).mulVec u =
      ![f4c (spkF (a1, a2) (b1, b2) (w1, w2)).1, f4c (spkF (a1, a2) (b1, b2) (w1, w2)).2] := by
  funext i
  fin_cases i
  · change _ = f4c (f4m a1 w1 ^^^ f4m b1 w2)
    rw [spk_f4c_xor _ (spk_f4m_lt _ _) _ (spk_f4m_lt _ _), spk_f4c_mul _ ha1 _ hw1,
      spk_f4c_mul _ hb1 _ hw2]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu0, hu1]
  · change _ = f4c (f4m a2 w1 ^^^ f4m b2 w2)
    rw [spk_f4c_xor _ (spk_f4m_lt _ _) _ (spk_f4m_lt _ _), spk_f4c_mul _ ha2 _ hw1,
      spk_f4c_mul _ hb2 _ hw2]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu0, hu1]

theorem spk_sigma {d : ℕ} (h : semOk (dec d) = true) {v : ℕ} (hv : v < 16) :
    psi4 (mulVecC (dec d) v) = RuType.sigmaAct (phiC (dec d)) (psi4 v) := by
  obtain ⟨hall, hdet⟩ := spk_semOk_facts h
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, hk⟩ := spk_semC_lt d
  obtain ⟨w1, w2⟩ := spk_psiC_lt v hv
  rw [phiC, dif_pos hdet]
  change psi4 (mulVecC (dec d) v) = (matC (dec d)).mulVec
    (RuType.frobVec (Multiplicative.ofAdd (((semC (dec d)).2.2 : ℕ) : ZMod 2)) (psi4 v))
  rw [← mv_eq]
  unfold psi4
  rw [hall v hv]
  change _ = (!![f4c (semC (dec d)).1.1, f4c (semC (dec d)).2.1.1; f4c (semC (dec d)).1.2,
    f4c (semC (dec d)).2.1.2]).mulVec _
  generalize (semC (dec d)).2.2 = k at hk ⊢
  interval_cases k
  · rw [spk_sig1 a1 a2 b1 b2 w1 w2 _ (by simp [RuType.frobVec]) (by simp [RuType.frobVec])]
    rfl
  · rw [spk_sig1 (w1 := frobC (psiC v).1) (w2 := frobC (psiC v).2) a1 a2 b1 b2 (spk_frobC_lt _)
      (spk_frobC_lt _) _
      (by simp [RuType.frobVec, spk_f4c_frob _ w1]) (by simp [RuType.frobVec, spk_f4c_frob _ w2])]
    rfl

theorem spk_permK (T P d : ℕ) :
    (∀ i < 5, appP (permK T P d) i = ptK P (psiK (mv d (psiInvK T (ptCode i))))) ∧
    ((∀ i < 5, appP (permK T P d) i = i) → permK T P d = idP) := by
  set g := fun i => ptK P (psiK (mv d (psiInvK T (ptCode i)))) with hgdef
  have hb := spk_pack (g 0) (spk_ptK_lt _ _) (g 1) (spk_ptK_lt _ _) (g 2) (spk_ptK_lt _ _)
    (g 3) (spk_ptK_lt _ _) (g 4) (spk_ptK_lt _ _)
  have hb' : spkPackB (permK T P d) (g 0) (g 1) (g 2) (g 3) (g 4) = true := hb
  unfold spkPackB at hb'
  obtain ⟨e0, hb'⟩ := bAnd_true hb'
  obtain ⟨e1, hb'⟩ := bAnd_true hb'
  obtain ⟨e2, hb'⟩ := bAnd_true hb'
  obtain ⟨e3, hb'⟩ := bAnd_true hb'
  obtain ⟨e4, e5⟩ := bAnd_true hb'
  have E : ∀ i < 5, appP (permK T P d) i = g i := by
    intro i hi
    interval_cases i
    · exact Nat.eq_of_beq_eq_true e0
    · exact Nat.eq_of_beq_eq_true e1
    · exact Nat.eq_of_beq_eq_true e2
    · exact Nat.eq_of_beq_eq_true e3
    · exact Nat.eq_of_beq_eq_true e4
  refine ⟨E, fun h => ?_⟩
  have hg : ∀ i < 5, g i = i := fun i hi => (E i hi).symm.trans (h i hi)
  rw [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num),
    hg 4 (by norm_num)] at e5
  exact Nat.eq_of_beq_eq_true (bIf_true e5 rfl)

theorem spk_permC {T P : ℕ} (ht : ∀ w < 16, psiInvK T w = psiInv (spkD w))
    (hp : ∀ w < 16, ptK P w = ptIdx (spkD w)) (d : ℕ) :
    permC (dec d) = [appP (permK T P d) 0, appP (permK T P d) 1, appP (permK T P d) 2,
      appP (permK T P d) 3, appP (permK T P d) 4] := by
  have key : ∀ i < 5, appP (permK T P d) i =
      ptIdx (psiC (mulVecC (dec d) (psiInv (pts.getD i (0, 0))))) := by
    intro i hi
    obtain ⟨h16, -, hpt, -⟩ := spk_pts i hi
    rw [(spk_permK T P d).1 i hi, ht _ h16, hpt, hp _ (spk_psiK_lt _ (mv_lt _ _)),
      spk_psiK _ (mv_lt _ _), spk_DE (spk_psiC_lt _ (mv_lt _ _)), mv_eq]
  rw [key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num), key 3 (by norm_num),
    key 4 (by norm_num)]
  rfl

theorem spk_permFacts {p : ℕ} (h : permOKK p = true) :
    PermCond [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4] ∧
    ([appP p 0, appP p 1, appP p 2, appP p 3, appP p 4].all (· < 5) &&
      decide [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4].Nodup) = true ∧
    ((∀ i, permOfList [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4] i = i) →
      [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4] = [0, 1, 2, 3, 4]) ∧
    (parK p = 0 →
      Equiv.Perm.sign (permOfList [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4]) = 1) := by
  obtain ⟨h1, -⟩ := bAnd_true h
  have hb := spk_perm5 _ (spk_appP_lt p 0) _ (spk_appP_lt p 1) _ (spk_appP_lt p 2) _
    (spk_appP_lt p 3) _ (spk_appP_lt p 4)
  unfold spkPermB at hb
  have hb2 := bIf_true hb h1
  obtain ⟨c1, hb2⟩ := bAnd_true hb2
  obtain ⟨c2, hb2⟩ := bAnd_true hb2
  obtain ⟨c3, c4⟩ := bAnd_true hb2
  refine ⟨of_decide_eq_true c1, c2,
    fun hi => of_decide_eq_true (bIf_true c3 (decide_eq_true hi)),
    fun hpar => of_decide_eq_true (bIf_true c4 ?_)⟩
  have e : spkPar (fun i => [appP p 0, appP p 1, appP p 2, appP p 3, appP p 4].getD i 0) = 0 :=
    hpar
  rw [e]
  rfl

theorem spk_lineMap {T P d p : ℕ} (h : lineMapK T P d p = true) {w : ℕ} (hw0 : 0 < w)
    (hw : w < 16) : ptK P (psiK (mv d (psiInvK T w))) = appP p (ptK P w) := by
  obtain ⟨j, rfl⟩ : ∃ j, w = j + 1 := ⟨w - 1, by omega⟩
  have := natAll (f := fun j => Nat.beq (ptK P (psiK (mv d (psiInvK T (Nat.succ j)))))
    (appP p (ptK P (Nat.succ j)))) 15 h j (by omega)
  exact Nat.eq_of_beq_eq_true this

theorem spk_hom {T P d e : ℕ} (ht : ∀ w < 16, psiInvK T w = psiInv (spkD w))
    (hd : lineMapK T P d (permK T P d) = true) (hinj : ∀ v < 16, mv e v = 0 → v = 0) {i : ℕ}
    (hi : i < 5) :
    appP (permK T P (mulP d e)) i = appP (permK T P d) (appP (permK T P e) i) := by
  rw [(spk_permK T P (mulP d e)).1 i hi, (spk_permK T P e).1 i hi]
  obtain ⟨hc16, hc0, -, -⟩ := spk_pts i hi
  have hu := spk_psiInvK_lt T (ptCode i)
  have hpu : psiK (psiInvK T (ptCode i)) = ptCode i := by
    rw [ht _ hc16]
    exact (spk_psiInv _ hc16).2
  have hu0 : psiInvK T (ptCode i) ≠ 0 := fun h0 => by
    rw [h0] at hpu
    have : psiK 0 = 0 := by decide
    omega
  have hu'0 : mv e (psiInvK T (ptCode i)) ≠ 0 := fun h0 => hu0 (hinj _ hu h0)
  have hlt := mv_lt e (psiInvK T (ptCode i))
  have hw' : 0 < psiK (mv e (psiInvK T (ptCode i))) := by
    rcases Nat.eq_zero_or_pos (psiK (mv e (psiInvK T (ptCode i)))) with h0 | h0
    · exact absurd (spk_psiK_inj _ hlt 0 (by norm_num) (h0.trans (by decide))) hu'0
    · exact h0
  have e2 := spk_lineMap hd hw' (spk_psiK_lt _ hlt)
  have e3 : psiInvK T (psiK (mv e (psiInvK T (ptCode i)))) = mv e (psiInvK T (ptCode i)) := by
    rw [ht _ (spk_psiK_lt _ hlt)]
    exact spk_psiInv_psiK _ hlt
  rw [← e2, e3, spk_mv_mul]

theorem spk_permOk {l : List ℕ}
    (h1 : ∀ d ∈ l, ∀ e ∈ l, permC (mulC (dec d) (dec e)) = compP (permC (dec d)) (permC (dec e)))
    (h2 : ∀ d ∈ l, permC (dec d) = [0, 1, 2, 3, 4] → dec d = oneC4)
    (h3 : ∀ d ∈ l, ((permC (dec d)).all (· < 5) && decide (permC (dec d)).Nodup) = true) :
    permOk (l.map dec) = true := by
  unfold permOk
  simp only [List.map_map, Bool.and_eq_true, List.all_eq_true, List.mem_map, Function.comp_apply,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, beq_iff_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true]
  refine ⟨⟨fun d hd e he => h1 d hd e he, fun d hd => ?_⟩, fun d hd => ?_⟩
  · by_cases hc : permC (dec d) = [0, 1, 2, 3, 4]
    · exact Or.inr (h2 d hd hc)
    · exact Or.inl hc
  · simpa using h3 d hd

theorem spk_c27 : (List.range 16).all (fun v => (psiC v).1 < 4 && (psiC v).2 < 4) = true := by
  decide +kernel

theorem spk_c32 : (List.range 16).all (fun v => (List.range 16).all fun w =>
    psiC v != psiC w || v == w) = true := by decide +kernel

theorem spk_c35 : decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16,
    psi4 (x ^^^ y) = psi4 x + psi4 y) = true := by decide +kernel

theorem spk_c36 : decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16, psi4 x = psi4 y → x = y) =
    true := by decide +kernel

theorem spk_p9 : (decide p9C.1.Nodup && p9C.1.all validB && closedB p9C.1 &&
    p9C.1.contains oneC4) = true := by decide +kernel

theorem spk_allc {b : Bool} {l : List Bool} (h1 : b = true) (h2 : l.all id = true) :
    (b :: l).all id = true := by
  rw [List.all_cons, h1, h2]
  rfl

theorem specialK_sound {spM : ℕ} {sp : SpecR} {A B S36 S120 P9 SP : List ℕ} {p9M : ℕ}
    {permL : List ℕ} {T P : ℕ} (he : elemsOK spM = true)
    (h : specialK spM sp A B S36 S120 P9 SP p9M permL T P = true) (hp9 : p9C.2 = p9M)
    (hp9m : p9C.2 = maskOf p9C.1) (hp9l : p9C.1.length = 9) :
    specialOk (specOf sp A B S36 S120) = true := by
  obtain ⟨k1, h⟩ := bAnd_true h
  obtain ⟨k2, h⟩ := bAnd_true h
  obtain ⟨k3, h⟩ := bAnd_true h
  obtain ⟨k4, h⟩ := bAnd_true h
  obtain ⟨k5, h⟩ := bAnd_true h
  obtain ⟨k6, h⟩ := bAnd_true h
  obtain ⟨k7, h⟩ := bAnd_true h
  obtain ⟨k8, h⟩ := bAnd_true h
  obtain ⟨k9, h⟩ := bAnd_true h
  obtain ⟨k10, h⟩ := bAnd_true h
  obtain ⟨k11, h⟩ := bAnd_true h
  obtain ⟨k12, h⟩ := bAnd_true h
  obtain ⟨k13, h⟩ := bAnd_true h
  obtain ⟨k14, h⟩ := bAnd_true h
  obtain ⟨k15, h⟩ := bAnd_true h
  obtain ⟨k20, h⟩ := bAnd_true h
  obtain ⟨k21, h⟩ := bAnd_true h
  obtain ⟨k22, h⟩ := bAnd_true h
  obtain ⟨k23, h⟩ := bAnd_true h
  obtain ⟨k24, h⟩ := bAnd_true h
  obtain ⟨k25, h⟩ := bAnd_true h
  obtain ⟨k26, h⟩ := bAnd_true h
  obtain ⟨k28, h⟩ := bAnd_true h
  obtain ⟨k29, h⟩ := bAnd_true h
  obtain ⟨k30, h⟩ := bAnd_true h
  obtain ⟨k31, h⟩ := bAnd_true h
  obtain ⟨k33, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨k37, h⟩ := bAnd_true h
  obtain ⟨k38, h⟩ := bAnd_true h
  obtain ⟨k39, h⟩ := bAnd_true h
  obtain ⟨k40, h⟩ := bAnd_true h
  obtain ⟨k41, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨k43, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨-, h⟩ := bAnd_true h
  obtain ⟨k47, h⟩ := bAnd_true h
  obtain ⟨k48, h⟩ := bAnd_true h
  obtain ⟨k49, h⟩ := bAnd_true h
  obtain ⟨k50, h⟩ := bAnd_true h
  obtain ⟨k51, h⟩ := bAnd_true h
  obtain ⟨k52, h⟩ := bAnd_true h
  obtain ⟨k53, h⟩ := bAnd_true h
  obtain ⟨k54, -⟩ := bAnd_true h
  obtain ⟨ht, hp⟩ := spk_tabs k54
  have hA := spk_inc k4
  have hB := spk_inc k5
  have hS36 := spk_inc k6
  have hS := spk_inc k7
  have ma : sp.2.1 = maskL A := Nat.eq_of_beq_eq_true k8
  have mb : sp.2.2.1 = maskL B := Nat.eq_of_beq_eq_true k9
  have ms36 : sp.1 = maskL S36 := Nat.eq_of_beq_eq_true k10
  have ms : sp.2.2.2.1 = maskL S120 := Nat.eq_of_beq_eq_true k11
  have mp9 : p9M = maskL P9 := Nat.eq_of_beq_eq_true k47
  have hsem : ∀ d ∈ S120, semOk (dec d) = true := fun d hd =>
    (spk_semOk ht).symm.trans (spk_allL k29 d hd)
  obtain ⟨b33a, b33b⟩ := bAnd_true k33
  obtain ⟨hlen, hz1⟩ := spk_all2 _ _ _ b33a
  have hz2 := (spk_all2 _ _ _ b33b).2
  have hz39 := (spk_all2 _ _ _ k39).2
  have hz40 := (spk_all2 _ _ _ k40).2
  have hperm : ∀ d ∈ S120, lineMapK T P d (permK T P d) = true ∧ permOKK (permK T P d) = true ∧
      (permK T P d = idP → d = oneP) ∧
      (fld(semK T d, 8, 1) = 0 → parK (permK T P d) = 0) := by
    intro d hd
    obtain ⟨p, hdp⟩ := spk_zip_left S120 permL hlen d hd
    have e : permK T P d = p := Nat.eq_of_beq_eq_true (hz1 d p hdp)
    rw [e]
    refine ⟨hz2 d p hdp, spk_allL k37 p (List.of_mem_zip hdp).2, fun hid => ?_, fun h8 => ?_⟩
    · have h39 : Bool.rec (motive := fun _ => Bool) true (Nat.beq d oneP) (Nat.beq p idP) = true :=
        hz39 d p hdp
      rw [hid] at h39
      exact Nat.eq_of_beq_eq_true (bIf_true h39 rfl)
    · have h40 : Bool.rec (motive := fun _ => Bool) true (Nat.beq (parK p) 0)
          (Nat.beq fld(semK T d, 8, 1) 0) = true := hz40 d p hdp
      rw [h8] at h40
      exact Nat.eq_of_beq_eq_true (bIf_true h40 rfl)
  have hpc := spk_permC ht hp
  have hQ := spk_p9
  simp only [Bool.and_eq_true] at hQ
  obtain ⟨⟨⟨q1, q2⟩, q3⟩, q4⟩ := hQ
  have hQv : ∀ x ∈ p9C.1, ValidC4 x := fun x hx => by
    have := List.all_eq_true.mp q2 x hx
    simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at this
    exact this
  have hQ1 : ∀ x ∈ p9C.1, codeC x ∈ P9 ∧ dec (codeC x) = x := fun x hx => ⟨by
      have := memM_maskOf_of_mem hx
      rw [← hp9m, hp9, mp9, memM, spk_maskL] at this
      exact this, dec_codeC (hQv x hx)⟩
  have hQ2 : ∀ c ∈ P9, dec c ∈ p9C.1 := fun c hc => by
    have h1 : (maskOf p9C.1).testBit c = true := by
      rw [← hp9m, hp9, mp9]
      exact spk_maskL.mpr hc
    rw [maskOf, testBit_foldl_addM] at h1
    simp only [Nat.zero_testBit, Bool.false_eq_true, false_or] at h1
    obtain ⟨y, hy, rfl⟩ := h1
    rw [dec_codeC (hQv y hy)]
    exact hy
  unfold specialOk specialChecks
  set_option simprocs false in
  dsimp only [specOf]
  refine spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_
    (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ (spk_allc ?_ rfl)))))))))))))))))))))))))))))
    )))))))))))))))))))))))
  · rw [List.length_map, ← spk_lenL]
    exact spk_nb k1
  · rw [List.length_map, ← spk_lenL]
    exact spk_nb k2
  · rw [List.length_map, ← spk_lenL]
    exact spk_nb k3
  · exact decide_eq_true (spk_nodup_map k4)
  · exact decide_eq_true (spk_nodup_map k5)
  · exact decide_eq_true (spk_nodup_map k6)
  · exact decide_eq_true (spk_nodup_map k7)
  · rw [spk_maskOf hA.1]
    exact spk_nb k8
  · rw [spk_maskOf hB.1]
    exact spk_nb k9
  · rw [spk_maskOf hS36.1]
    exact spk_nb k10
  · rw [spk_maskOf hS.1]
    exact spk_nb k11
  · obtain ⟨x, hx, h1⟩ := spk_anyL k12
    obtain ⟨y, hy, h2⟩ := spk_anyL h1
    refine spk_any_map hx (spk_any_map hy ?_)
    beta_reduce
    rw [bne, ← spk_commK, bNot_true h2]
    rfl
  · obtain ⟨x, hx, h1⟩ := spk_anyL k13
    obtain ⟨y, hy, h2⟩ := spk_anyL h1
    refine spk_any_map hx (spk_any_map hy ?_)
    beta_reduce
    rw [bne, ← spk_commK, bNot_true h2]
    rfl
  · refine spk_all_map fun x hx => spk_all_map fun y hy => ?_
    beta_reduce
    rw [← spk_commK]
    exact spk_allL (spk_allL k14 x hx) y hy
  · refine spk_all_map fun x hx => ?_
    beta_reduce
    rw [spk_memM (hA.1 x hx), ← dec_oneP, spk_beq_dec (hA.1 x hx) spk_oneP_lt]
    exact spk_imp (spk_allL k15 x hx)
  · exact spk_all_map fun x _ => spk_validB x
  · exact spk_all_map fun x _ => spk_validB x
  · exact spk_all_map fun x _ => spk_validB x
  · exact spk_all_map fun x _ => spk_validB x
  · unfold closedB
    refine spk_all_map fun x hx => spk_all_map fun y hy => ?_
    beta_reduce
    rw [← dec_mulP]
    have h1 := spk_allL (spk_allL k20 x hx) y hy
    beta_reduce at h1
    rw [ma, memP_eq, spk_maskL] at h1
    exact spk_contains_map h1
  · unfold closedB
    refine spk_all_map fun x hx => spk_all_map fun y hy => ?_
    beta_reduce
    rw [← dec_mulP]
    have h1 := spk_allL (spk_allL k21 x hx) y hy
    beta_reduce at h1
    rw [mb, memP_eq, spk_maskL] at h1
    exact spk_contains_map h1
  · rw [← dec_oneP]
    have h1 := k22
    rw [ma, memP_eq, spk_maskL] at h1
    exact spk_contains_map h1
  · rw [← dec_oneP]
    have h1 := k23
    rw [mb, memP_eq, spk_maskL] at h1
    exact spk_contains_map h1
  · refine spk_all_map fun x hx => ?_
    rw [spk_memM (hA.1 x hx), memP_eq]
    exact subP_bit k24 (by rw [ma]; exact spk_maskL.mpr hx)
  · refine spk_all_map fun x hx => ?_
    rw [spk_memM (hB.1 x hx), memP_eq]
    exact subP_bit k25 (by rw [mb]; exact spk_maskL.mpr hx)
  · unfold closedB
    rw [List.all_eq_true]
    intro x' hx'
    obtain ⟨hx', hm⟩ := List.mem_filter.mp hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hx'
    rw [List.all_eq_true]
    intro y' hy'
    obtain ⟨hy', hmy⟩ := List.mem_filter.mp hy'
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hy'
    rw [spk_memM (hS.1 x hx)] at hm
    rw [spk_memM (hS.1 y hy)] at hmy
    have hxy : mulP x y ∈ S120 := by
      have h1 := spk_allL (spk_allL k38 x hx) y hy
      beta_reduce at h1
      rw [ms, memP_eq, spk_maskL] at h1
      exact h1
    have hm2 : memP sp.2.2.2.2 (mulP x y) = true :=
      bIf_true (spk_allL (bIf_true (spk_allL k26 x hx) hm) y hy) hmy
    rw [← dec_mulP]
    exact List.elem_eq_true_of_mem (List.mem_filter.mpr ⟨List.mem_map_of_mem hxy, by
      rw [spk_memM (mulP_lt _ _)]
      exact hm2⟩)
  · exact spk_c27
  · rw [List.length_map, ← spk_lenL]
    exact spk_nb k28
  · exact spk_all_map hsem
  · have h30 : Nat.beq sp.2.2.2.2 (maskL (S120.filter fun x => Nat.beq fld(semK T x, 8, 1) 0)) =
        true := by
      rw [← spk_filterRec]
      exact k30
    have hf : (S120.map dec).filter (fun d => (semC d).2.2 == 0) =
        (S120.filter fun x => Nat.beq fld(semK T x, 8, 1) 0).map dec := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro x _
      simp only [Function.comp_apply]
      rw [(spk_sem (d := x) ht).2.2.1, spk_nbeq]
    rw [hf, spk_maskOf (fun x hx => hS.1 x (List.mem_of_mem_filter hx))]
    exact spk_nb h30
  · have hf : (S120.map dec).filter (memM sp.2.2.2.2) =
        (S120.filter (memP sp.2.2.2.2)).map dec := by
      rw [List.filter_map]
      congr 1
      apply List.filter_congr
      intro x hx
      simp only [Function.comp_apply]
      exact spk_memM (hS.1 x hx)
    rw [hf, List.length_map, ← spk_cntL]
    exact spk_nb k31
  · exact spk_c32
  · refine spk_permOk (fun d hd e he => ?_) (fun d hd hc => ?_) (fun d hd => ?_)
    · have hinj := spk_inj (hsem e he)
      have he5 := (Bool.and_eq_true _ _).mp (spk_permFacts (hperm e he).2.1).2.1
      have hlt : ∀ i < 5, appP (permK T P e) i < 5 := fun i hi => by
        have := List.all_eq_true.mp he5.1 (appP (permK T P e) i) (by interval_cases i <;> simp)
        simpa using this
      rw [← dec_mulP, hpc (mulP d e), hpc d, hpc e]
      simp only [compP, List.map_cons, List.map_nil]
      rw [spk_hom ht (hperm d hd).1 hinj (i := 0) (by norm_num),
        spk_hom ht (hperm d hd).1 hinj (i := 1) (by norm_num),
        spk_hom ht (hperm d hd).1 hinj (i := 2) (by norm_num),
        spk_hom ht (hperm d hd).1 hinj (i := 3) (by norm_num),
        spk_hom ht (hperm d hd).1 hinj (i := 4) (by norm_num),
        spk_getD5 (appP (permK T P d)) (hlt 0 (by norm_num)),
        spk_getD5 (appP (permK T P d)) (hlt 1 (by norm_num)),
        spk_getD5 (appP (permK T P d)) (hlt 2 (by norm_num)),
        spk_getD5 (appP (permK T P d)) (hlt 3 (by norm_num)),
        spk_getD5 (appP (permK T P d)) (hlt 4 (by norm_num))]
    · rw [hpc d] at hc
      simp only [List.cons.injEq] at hc
      obtain ⟨h0, h1', h2, h3, h4, -⟩ := hc
      have hid := (spk_permK T P d).2 (fun i hi => by interval_cases i <;> assumption)
      rw [(hperm d hd).2.2.1 hid]
      exact dec_oneP
    · rw [hpc d]
      exact (spk_permFacts (hperm d hd).2.1).2.1
  · apply decide_eq_true
    intro d' hd' v hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    exact spk_sigma (hsem d hd) (List.mem_range.mp hv)
  · exact spk_c35
  · exact spk_c36
  · apply decide_eq_true
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    rw [hpc d]
    exact (spk_permFacts (hperm d hd).2.1).1
  · refine spk_all_map fun x hx => spk_all_map fun y hy => ?_
    rw [← dec_mulP, spk_memM (mulP_lt _ _)]
    exact spk_allL (spk_allL k38 x hx) y hy
  · apply decide_eq_true
    intro d' hd' h1
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    have hL := (spk_permFacts (hperm d hd).2.1).2.2.1 (fun i => by
      rw [← hpc d]
      exact congrArg (fun σ : Equiv.Perm (Fin 5) => σ i) h1)
    simp only [List.cons.injEq] at hL
    obtain ⟨h0, h1', h2, h3, h4, -⟩ := hL
    have hid := (spk_permK T P d).2 (fun i hi => by interval_cases i <;> assumption)
    rw [(hperm d hd).2.2.1 hid]
    exact dec_oneP
  · apply decide_eq_true
    intro d' hd' hr
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    obtain ⟨-, hdet⟩ := spk_semOk_facts (hsem d hd)
    rw [phiC, dif_pos hdet] at hr
    have hk := (spk_right _ (spk_semC_lt d).2.2).mp hr
    have h8 : fld(semK T d, 8, 1) = 0 := (spk_sem (d := d) ht).2.2.1.trans hk
    have := (spk_permFacts (hperm d hd).2.1).2.2.2 ((hperm d hd).2.2.2 h8)
    rw [permF, hpc d]
    exact this
  · apply decide_eq_true
    intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    obtain ⟨-, hdet⟩ := spk_semOk_facts (hsem d hd)
    rw [spk_memM (hS.1 d hd), phiC, dif_pos hdet]
    have hk2 := (spk_semC_lt d).2.2
    have hk := spk_allL k41 d hd
    beta_reduce at hk
    rw [(spk_sem (d := d) ht).2.2.1] at hk
    change memP sp.2.2.2.2 d =
      decide (Multiplicative.ofAdd (((semC (dec d)).2.2 : ℕ) : ZMod 2) = 1)
    cases hm : memP sp.2.2.2.2 d
    · rw [hm] at hk
      have h1 := Nat.eq_of_beq_eq_true hk
      exact (decide_eq_false fun h' => by
        have := (spk_right _ hk2).mp h'
        omega).symm
    · rw [hm] at hk
      exact (decide_eq_true ((spk_right _ hk2).mpr (Nat.eq_of_beq_eq_true hk))).symm
  · rw [hp9l]
    rfl
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · rw [← hp9m]
    exact beq_self_eq_true _
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨hc, hdx⟩ := hQ1 x hx
    rw [← hdx]
    apply spk_contains_map
    have h1 := subP_bit k48 (by rw [mp9]; exact spk_maskL.mpr hc)
    rw [ms36] at h1
    exact spk_maskL.mp h1
  · refine spk_all_map fun g hg => ?_
    beta_reduce
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨hc, hdx⟩ := hQ1 x hx
    obtain ⟨y, hy, hxy⟩ := spk_anyL (spk_allL (spk_allL k49 g hg) _ hc)
    rw [List.any_eq_true]
    refine ⟨dec y, hQ2 y hy, ?_⟩
    rw [← hdx, ← dec_mulP, ← dec_mulP, Nat.eq_of_beq_eq_true hxy]
    exact beq_self_eq_true _
  · refine spk_all_map fun x hx => ?_
    beta_reduce
    rw [spk_ord3 (hS36.1 x hx)]
    have h1 := spk_allL k50 x hx
    beta_reduce at h1
    cases ho : ord3K x
    · rfl
    · rw [ho] at h1
      have h2 : memP p9M x = true := h1
      rw [mp9, memP_eq, spk_maskL] at h2
      exact List.elem_eq_true_of_mem (hQ2 x h2)
  · rw [List.all_eq_true]
    intro x hx
    rw [List.all_eq_true]
    intro y hy
    obtain ⟨cx, hdx⟩ := hQ1 x hx
    obtain ⟨cy, hdy⟩ := hQ1 y hy
    rw [← hdx, ← hdy, ← spk_commK]
    exact spk_allL (spk_allL k51 _ cx) _ cy
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨cx, hdx⟩ := hQ1 x hx
    rw [← hdx, ← dec_oneP, ← dec_mulP, ← dec_mulP, spk_beq_dec (mulP_lt _ _) spk_oneP_lt]
    exact spk_allL k52 _ cx
  · obtain ⟨s1, s2⟩ := bAnd_true k53
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨hv, hsy⟩ := mem_spElsC.mp hx
    have hc := codeC_lt hv
    have hdx := dec_codeC hv
    have hm : memP spM (codeC x) = true :=
      (elemsOK_sound he _).mpr ⟨hc, by rw [isSympK_eq, hdx]; exact hsy⟩
    rw [← Nat.eq_of_beq_eq_true s1, memP_eq, spk_maskL] at hm
    have h1 := spk_allL s2 _ hm
    rw [← hdx, ← spk_powK, ← dec_oneP, ← dec_mulP, ← dec_mulP, bne,
      spk_beq_dec (spk_powK_lt _ _) spk_oneP_lt, spk_beq_dec (mulP_lt _ _) spk_oneP_lt]
    exact spk_imp h1

end SpecialK

end CFSG.KD.Sp4Ov

end
