module

public import Certificates.Data.Kernel.AS35QTS.Checks
public import CFSG.LargeExtraspecial.AS35QTSCode

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd V3 M3 mulC mv mm rowMul dot vadd betaC hermC tr2C fr)

variable {α β : Type}

@[expose] def dotL (o : Ops α) (u v : V3T α) : α :=
  dl o u.l0 u.h0 v.l0 v.h0 u.l1 u.h1 v.l1 v.h1 u.l2 u.h2 v.l2 v.h2

@[expose] def dotH (o : Ops α) (u v : V3T α) : α :=
  dh o u.l0 u.h0 v.l0 v.h0 u.l1 u.h1 v.l1 v.h1 u.l2 u.h2 v.l2 v.h2

@[expose] def mvD (o : Ops α) (r0 r1 r2 v : V3T α) : V3T α :=
  ⟨dotL o r0 v, dotH o r0 v, dotL o r1 v, dotH o r1 v, dotL o r2 v, dotH o r2 v⟩

@[expose] def rowD (o : Ops α) (r c0 c1 c2 : V3T α) : V3T α :=
  ⟨dotL o r c0, dotH o r c0, dotL o r c1, dotH o r c1, dotL o r c2, dotH o r c2⟩

@[expose] def mulD (o : Ops α) (X Y : PL α) : PL α :=
  ⟨o.x (o.x X.e Y.e) (betaT o X.a (mvD o X.r0 X.r1 X.r2 Y.a)),
    ⟨o.x X.a.l0 (mvD o X.r0 X.r1 X.r2 Y.a).l0, o.x X.a.h0 (mvD o X.r0 X.r1 X.r2 Y.a).h0,
      o.x X.a.l1 (mvD o X.r0 X.r1 X.r2 Y.a).l1, o.x X.a.h1 (mvD o X.r0 X.r1 X.r2 Y.a).h1,
      o.x X.a.l2 (mvD o X.r0 X.r1 X.r2 Y.a).l2, o.x X.a.h2 (mvD o X.r0 X.r1 X.r2 Y.a).h2⟩,
    rowD o X.r0 (col0 Y) (col1 Y) (col2 Y), rowD o X.r1 (col0 Y) (col1 Y) (col2 Y),
    rowD o X.r2 (col0 Y) (col1 Y) (col2 Y)⟩

theorem mulK_eq (o : Ops α) {bd : α → (α → β) → β} (hbd : ∀ y k, bd y k = k y) (X Y : PL α)
    (k : PL α → β) : mulK o bd X Y k = k (mulD o X Y) := by
  simp only [mulK, mvK, rowK, entV, hbd, mulD, mvD, rowD, dotL, dotH]

@[expose] def bOps : Ops Bool := ⟨and, xor, true, fun y k => k y⟩

@[expose] def lb (x : F4) : Bool := x.code.val.testBit 0

@[expose] def hb (x : F4) : Bool := x.code.val.testBit 1

@[expose] def eb (e : ZMod 2) : Bool := decide (e = 1)

@[expose] def ofV (v : V3) : V3T Bool := ⟨lb v.x0, hb v.x0, lb v.x1, hb v.x1, lb v.x2, hb v.x2⟩

@[expose] def ofCd (c : Cd) : PL Bool := ⟨eb c.e, ofV c.a, ofV c.m.r0, ofV c.m.r1, ofV c.m.r2⟩

theorem pl_e : ∀ x y : F4, pl bOps (lb x) (hb x) (lb y) (hb y) = lb (x * y) := by decide

theorem ph_e : ∀ x y : F4, ph bOps (lb x) (hb x) (lb y) (hb y) = hb (x * y) := by decide

theorem plf_e : ∀ x y : F4, pl bOps (bOps.x (lb x) (hb x)) (hb x) (lb y) (hb y) = lb (fr x * y) := by
  decide

theorem phf_e : ∀ x y : F4, ph bOps (bOps.x (lb x) (hb x)) (hb x) (lb y) (hb y) = hb (fr x * y) := by
  decide

theorem xl_e : ∀ x y : F4, bOps.x (lb x) (lb y) = lb (x + y) := by decide

theorem xh_e : ∀ x y : F4, bOps.x (hb x) (hb y) = hb (x + y) := by decide

theorem xe_e (a b : ZMod 2) : bOps.x (eb a) (eb b) = eb (a + b) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem dotL_e (u v : V3) : dotL bOps (ofV u) (ofV v) = lb (dot u v) := by
  simp only [dotL, ofV, dl, pl_e, xl_e, dot]

theorem dotH_e (u v : V3) : dotH bOps (ofV u) (ofV v) = hb (dot u v) := by
  simp only [dotH, ofV, dh, ph_e, xh_e, dot]

theorem hL_e (u v : V3) : hL bOps (ofV u) (ofV v) = lb (hermC u v) := by
  simp only [hL, ofV, dl, plf_e, xl_e, hermC]

theorem hH_e (u v : V3) : hH bOps (ofV u) (ofV v) = hb (hermC u v) := by
  simp only [hH, ofV, dh, phf_e, xh_e, hermC]

theorem mvD_e (A : M3) (v : V3) :
    mvD bOps (ofV A.r0) (ofV A.r1) (ofV A.r2) (ofV v) = ofV (mv A v) := by
  simp only [mvD, dotL_e, dotH_e]
  rfl

theorem rowD_e (r : V3) (z : Cd) :
    rowD bOps (ofV r) (col0 (ofCd z)) (col1 (ofCd z)) (col2 (ofCd z)) = ofV (rowMul r z.m) := by
  have h0 : col0 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col0 z.m) := rfl
  have h1 : col1 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col1 z.m) := rfl
  have h2 : col2 (ofCd z) = ofV (CFSG.LargeExtraspecial.AS35QTS.col2 z.m) := rfl
  rw [h0, h1, h2]
  simp only [rowD, dotL_e, dotH_e]
  rfl

theorem tr_e (c : F4) : bOps.x (lb c) (hb c) = eb (tr2C (F4.ω * c)) := by
  obtain ⟨c⟩ := c
  fin_cases c <;> unfold tr2C <;> split_ifs with h <;>
    first
    | rfl
    | exact absurd rfl h
    | exact absurd (congrArg F4.code h) (by decide)

theorem betaT_e (u w : V3) : betaT bOps (ofV u) (ofV w) = eb (betaC u w) := by
  rw [betaT, hL_e, hH_e, tr_e]
  rfl

theorem mulD_ofCd (x y : Cd) : mulD bOps (ofCd x) (ofCd y) = ofCd (mulC x y) := by
  have hm : mvD bOps (ofCd x).r0 (ofCd x).r1 (ofCd x).r2 (ofCd y).a = ofV (mv x.m y.a) :=
    mvD_e x.m y.a
  have h0 : rowD bOps (ofCd x).r0 (col0 (ofCd y)) (col1 (ofCd y)) (col2 (ofCd y)) =
      ofV (rowMul x.m.r0 y.m) := rowD_e x.m.r0 y
  have h1 : rowD bOps (ofCd x).r1 (col0 (ofCd y)) (col1 (ofCd y)) (col2 (ofCd y)) =
      ofV (rowMul x.m.r1 y.m) := rowD_e x.m.r1 y
  have h2 : rowD bOps (ofCd x).r2 (col0 (ofCd y)) (col1 (ofCd y)) (col2 (ofCd y)) =
      ofV (rowMul x.m.r2 y.m) := rowD_e x.m.r2 y
  have hb : betaT bOps (ofCd x).a (ofV (mv x.m y.a)) = eb (betaC x.a (mv x.m y.a)) :=
    betaT_e x.a (mv x.m y.a)
  rw [mulD, hm, h0, h1, h2, hb]
  simp only [ofCd, ofV, mulC, vadd, mm, xe_e, xl_e, xh_e]

@[expose] def laneOf (c : Nat) (X : PL Nat) : PL Bool := mapP (fun p => p.testBit c) X

theorem tb_land (p q c : Nat) : (Nat.land p q).testBit c = (p.testBit c && q.testBit c) :=
  Nat.testBit_land p q c

theorem tb_xor (p q c : Nat) : (Nat.xor p q).testBit c = xor (p.testBit c) (q.testBit c) :=
  Nat.testBit_xor p q c

theorem lane_mulD (t c : Nat) (X Y : PL Nat) :
    laneOf c (mulD (natOps t) X Y) = mulD bOps (laneOf c X) (laneOf c Y) := by
  simp only [laneOf, mapP, mulD, mvD, rowD, dotL, dotH, dl, dh, pl, ph, betaT, hL, hH, col0, col1,
    col2, natOps, bOps, tb_land, tb_xor]

theorem lane_mulP (t c : Nat) {X Y : PL Nat} {x y : Cd} (hX : laneOf c X = ofCd x)
    (hY : laneOf c Y = ofCd y) : laneOf c (mulD (natOps t) X Y) = ofCd (mulC x y) := by
  rw [lane_mulD, hX, hY, mulD_ofCd]

end CFSG.KC.AS35QTS

end
