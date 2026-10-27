module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GH74.QTGen4.Leaves.G112

structure Lin where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat

@[expose] def ap (m : Lin) (v : Nat) : Nat :=
  (if v.testBit 0 then m.c0 else 0) ^^^ (if v.testBit 1 then m.c1 else 0) ^^^
    (if v.testBit 2 then m.c2 else 0) ^^^ (if v.testBit 3 then m.c3 else 0)

@[expose] def comp (m n : Lin) : Lin := ⟨ap m n.c0, ap m n.c1, ap m n.c2, ap m n.c3⟩

@[expose] def idL : Lin := ⟨1, 2, 4, 8⟩

@[expose] def bf (x y : Nat) : Bool :=
  ((x.testBit 0 && y.testBit 3) ^^ (x.testBit 3 && y.testBit 0)) ^^
    ((x.testBit 1 && y.testBit 2) ^^ (x.testBit 2 && y.testBit 1))

@[expose] def tL : Lin := ⟨1, 2, 5, 10⟩

@[expose] def Wit (h : Lin) : Bool :=
  (decide (ap h 0 < 4) && decide (ap h 1 < 4) && decide (ap h 2 < 4) && decide (ap h 3 < 4)) &&
    decide (ap h 1 ≠ 1)

@[expose] def pw2 (g : Lin) : Lin := comp g g

@[expose] def cube (g : Lin) : Lin := comp g (pw2 g)

@[expose] def eqL (m n : Lin) : Bool := m.c0 == n.c0 && m.c1 == n.c1 && m.c2 == n.c2 && m.c3 == n.c3

@[expose] def w5a (g : Lin) : Lin :=
  comp g (comp tL (comp (comp (pw2 g) (pw2 g)) (comp tL g)))

@[expose] def w5b (g : Lin) : Lin :=
  comp (pw2 g) (comp tL (comp (cube g) (comp tL (pw2 g))))

@[expose] def allSp (P : Lin → Bool) : Bool :=
  (List.range 16).all fun c0 => (List.range 16).all fun c1 =>
    !(bf c0 c1 == false) || (List.range 16).all fun c2 =>
      !(bf c0 c2 == false && bf c1 c2 == true) || (List.range 16).all fun c3 =>
        !(bf c0 c3 == true && bf c1 c3 == false && bf c2 c3 == false) || P ⟨c0, c1, c2, c3⟩

@[expose] def P5 (g : Lin) : Bool :=
  !(eqL (comp (pw2 g) (cube g)) idL && !eqL g idL) || Wit (w5a g) || Wit (w5b g)

theorem core5 : allSp P5 = true := by
  decide +kernel

@[expose] def P9a (x : Lin) : Bool := !eqL (cube (cube x)) idL || eqL (cube x) idL

theorem nine : allSp P9a = true := by
  decide +kernel

@[expose] def W9 (a b : Lin) : Bool :=
  let c := comp a b
  Wit (comp a (comp tL (comp (pw2 a) (comp tL a)))) ||
  Wit (comp b (comp tL (comp b (comp tL (comp (pw2 b) (comp tL (pw2 b))))))) ||
  Wit (comp c (comp tL (comp (pw2 c) (comp tL c)))) ||
  Wit (comp a (comp tL (pw2 a))) ||
  Wit (comp c (comp tL (pw2 c)))

@[expose] def ord3 : List Lin := [
  ⟨1, 4, 6, 8⟩,
  ⟨1, 4, 7, 13⟩,
  ⟨1, 5, 6, 15⟩,
  ⟨1, 5, 7, 11⟩,
  ⟨1, 6, 2, 8⟩,
  ⟨1, 6, 3, 15⟩,
  ⟨1, 7, 2, 11⟩,
  ⟨1, 7, 3, 13⟩,
  ⟨2, 3, 8, 12⟩,
  ⟨2, 3, 9, 15⟩,
  ⟨2, 3, 10, 13⟩,
  ⟨2, 3, 11, 14⟩,
  ⟨3, 1, 12, 4⟩,
  ⟨3, 1, 13, 7⟩,
  ⟨3, 1, 14, 5⟩,
  ⟨3, 1, 15, 6⟩,
  ⟨4, 8, 5, 10⟩,
  ⟨4, 9, 5, 15⟩,
  ⟨4, 12, 5, 11⟩,
  ⟨4, 13, 5, 14⟩,
  ⟨5, 10, 1, 2⟩,
  ⟨5, 11, 1, 7⟩,
  ⟨5, 14, 1, 3⟩,
  ⟨5, 15, 1, 6⟩,
  ⟨6, 8, 15, 10⟩,
  ⟨6, 9, 14, 13⟩,
  ⟨6, 14, 9, 11⟩,
  ⟨6, 15, 8, 12⟩,
  ⟨7, 10, 11, 2⟩,
  ⟨7, 11, 10, 5⟩,
  ⟨7, 12, 13, 3⟩,
  ⟨7, 13, 12, 4⟩,
  ⟨8, 2, 4, 9⟩,
  ⟨8, 2, 14, 11⟩,
  ⟨8, 4, 6, 9⟩,
  ⟨8, 6, 2, 9⟩,
  ⟨8, 12, 10, 15⟩,
  ⟨8, 14, 4, 13⟩,
  ⟨9, 2, 4, 1⟩,
  ⟨9, 2, 15, 3⟩,
  ⟨9, 4, 6, 1⟩,
  ⟨9, 6, 2, 1⟩,
  ⟨9, 13, 11, 7⟩,
  ⟨9, 15, 4, 5⟩,
  ⟨10, 2, 7, 11⟩,
  ⟨10, 2, 15, 9⟩,
  ⟨10, 5, 13, 14⟩,
  ⟨10, 7, 8, 12⟩,
  ⟨10, 13, 15, 3⟩,
  ⟨10, 15, 2, 3⟩,
  ⟨11, 2, 7, 1⟩,
  ⟨11, 2, 14, 3⟩,
  ⟨11, 5, 12, 4⟩,
  ⟨11, 7, 9, 6⟩,
  ⟨11, 12, 14, 8⟩,
  ⟨11, 14, 2, 8⟩,
  ⟨12, 4, 15, 5⟩,
  ⟨12, 7, 4, 13⟩,
  ⟨12, 8, 7, 10⟩,
  ⟨12, 11, 3, 14⟩,
  ⟨12, 15, 4, 9⟩,
  ⟨12, 15, 11, 5⟩,
  ⟨13, 4, 14, 8⟩,
  ⟨13, 7, 4, 1⟩,
  ⟨13, 9, 7, 6⟩,
  ⟨13, 10, 3, 2⟩,
  ⟨13, 14, 4, 5⟩,
  ⟨13, 14, 10, 8⟩,
  ⟨14, 5, 3, 15⟩,
  ⟨14, 6, 11, 7⟩,
  ⟨14, 8, 13, 10⟩,
  ⟨14, 11, 8, 12⟩,
  ⟨14, 13, 6, 7⟩,
  ⟨14, 13, 11, 9⟩,
  ⟨15, 5, 3, 1⟩,
  ⟨15, 6, 10, 8⟩,
  ⟨15, 9, 12, 4⟩,
  ⟨15, 10, 9, 2⟩,
  ⟨15, 12, 6, 8⟩,
  ⟨15, 12, 10, 7⟩]

@[expose] def isOrd3 (a : Lin) : Bool := eqL (cube a) idL && !eqL a idL

@[expose] def inOrd3 (a : Lin) : Bool := ord3.any (eqL a)

theorem ord3_complete : allSp (fun a => !isOrd3 a || inOrd3 a) = true := by
  decide +kernel

@[expose] def pairOK (a b : Lin) : Bool :=
  !(eqL (comp a b) (comp b a) && !eqL b a && !eqL b (pw2 a)) || W9 a b

theorem pairs_ok : ord3.all (fun a => ord3.all (fun b => pairOK a b)) = true := by
  decide +kernel

@[expose] def IsoCols (g : Lin) : Prop :=
  g.c0 < 16 ∧ g.c1 < 16 ∧ g.c2 < 16 ∧ g.c3 < 16 ∧ bf g.c0 g.c1 = false ∧ bf g.c0 g.c2 = false ∧
    bf g.c1 g.c2 = true ∧ bf g.c0 g.c3 = true ∧ bf g.c1 g.c3 = false ∧ bf g.c2 g.c3 = false

theorem allSp_spec {P : Lin → Bool} (h : allSp P = true) {g : Lin} (hg : IsoCols g) :
    P g = true := by
  obtain ⟨h0, h1, h2, h3, h01, h02, h12, h03, h13, h23⟩ := hg
  have e0 := (List.all_eq_true.1 h) g.c0 (List.mem_range.2 h0)
  have e1 := (List.all_eq_true.1 e0) g.c1 (List.mem_range.2 h1)
  simp only [h01, beq_self_eq_true, Bool.not_true, Bool.false_or] at e1
  have e2 := (List.all_eq_true.1 e1) g.c2 (List.mem_range.2 h2)
  simp only [h02, h12, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at e2
  have e3 := (List.all_eq_true.1 e2) g.c3 (List.mem_range.2 h3)
  simp only [h03, h13, h23, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or] at e3
  exact e3

theorem eqL_eq {a b : Lin} (h : eqL a b = true) : a = b := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  obtain ⟨b0, b1, b2, b3⟩ := b
  simp only [eqL, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  subst h0 h1 h2 h3
  rfl

theorem eqL_self (a : Lin) : eqL a a = true := by
  simp [eqL]

theorem witness5 {g : Lin} (hg : IsoCols g) (h5 : eqL (comp (pw2 g) (cube g)) idL = true)
    (hne : eqL g idL = false) : Wit (w5a g) = true ∨ Wit (w5b g) = true := by
  have h := allSp_spec core5 hg
  simp only [P5, h5, hne, Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true] at h
  exact h

theorem witness9 {a b : Lin} (ha : IsoCols a) (hb : IsoCols b)
    (ha3 : eqL (cube a) idL = true) (ha1 : eqL a idL = false)
    (hb3 : eqL (cube b) idL = true) (hb1 : eqL b idL = false)
    (hab : eqL (comp a b) (comp b a) = true) (hba : eqL b a = false)
    (hba2 : eqL b (pw2 a) = false) : W9 a b = true := by
  have hA := allSp_spec ord3_complete ha
  have hB := allSp_spec ord3_complete hb
  have hoa : isOrd3 a = true := by simp [isOrd3, ha3, ha1]
  have hob : isOrd3 b = true := by simp [isOrd3, hb3, hb1]
  simp only [hoa, Bool.not_true, Bool.false_or] at hA
  simp only [hob, Bool.not_true, Bool.false_or] at hB
  simp only [inOrd3, List.any_eq_true] at hA hB
  obtain ⟨x, hx, hxa⟩ := hA
  obtain ⟨y, hy, hyb⟩ := hB
  have hxa' := eqL_eq hxa
  have hyb' := eqL_eq hyb
  have hxy := List.all_eq_true.1 (List.all_eq_true.1 pairs_ok x hx) y hy
  subst hxa' hyb'
  simp only [pairOK, hab, hba, hba2, Bool.and_self, Bool.not_true, Bool.not_false,
    Bool.false_or] at hxy
  exact hxy

theorem no_order_nine {x : Lin} (hx : IsoCols x) (h9 : eqL (cube (cube x)) idL = true) :
    eqL (cube x) idL = true := by
  have h := allSp_spec nine hx
  simp only [P9a, h9, Bool.not_true, Bool.false_or] at h
  exact h

@[expose] def encC (c : Fin 4 → ZMod 2) : Nat :=
  (c 0).val + 2 * (c 1).val + 4 * (c 2).val + 8 * (c 3).val

theorem encC_lt (c : Fin 4 → ZMod 2) : encC c < 16 := by
  revert c; decide

theorem encC_inj : ∀ c d : Fin 4 → ZMod 2, encC c = encC d → c = d := by
  decide

theorem encC_add : ∀ c d : Fin 4 → ZMod 2, encC (c + d) = encC c ^^^ encC d := by
  decide

theorem encC_smul : ∀ (a : ZMod 2) (c : Fin 4 → ZMod 2),
    encC (a • c) = if a = 1 then encC c else 0 := by
  decide

theorem encC_testBit : ∀ (c : Fin 4 → ZMod 2) (i : Fin 4), (encC c).testBit i = decide (c i = 1) := by
  decide

theorem encC_single (i : Fin 4) : encC (Pi.single i 1) = 2 ^ (i : Nat) := by
  fin_cases i <;> decide

end CFSG.GH74.QTGen4.Leaves.G112
