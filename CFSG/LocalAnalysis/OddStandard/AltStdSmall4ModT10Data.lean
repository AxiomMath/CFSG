module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.AltStdSmall4.ModT10

@[ext] structure T10 where
  x0 : ZMod 2
  x1 : ZMod 2
  x2 : ZMod 2
  x3 : ZMod 2
  x4 : ZMod 2
  x5 : ZMod 2
  s : ZMod 2
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
deriving DecidableEq

namespace T10

instance : Mul T10 := ⟨fun p q =>
  let y0 := q.x0 + p.a * q.x1 + p.b * q.x2
  let y1 := q.x1 + p.c * q.x2
  let y3 := q.x3 + p.a * q.x4 + p.b * q.x5
  let y4 := q.x4 + p.c * q.x5
  ⟨p.x0 + y0 + p.s * y3, p.x1 + y1 + p.s * y4, p.x2 + q.x2 + p.s * q.x5, p.x3 + y3, p.x4 + y4,
    p.x5 + q.x5, p.s + q.s, p.a + q.a, p.b + q.b + p.a * q.c, p.c + q.c⟩⟩

instance : One T10 := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Inv T10 := ⟨fun p =>
  let b' := -p.b + p.a * p.c
  let z0 := p.x0 - p.a * p.x1 + b' * p.x2
  let z1 := p.x1 - p.c * p.x2
  let z3 := p.x3 - p.a * p.x4 + b' * p.x5
  let z4 := p.x4 - p.c * p.x5
  ⟨-(z0 - p.s * z3), -(z1 - p.s * z4), -(p.x2 - p.s * p.x5), -z3, -z4, -p.x5, -p.s, -p.a, b',
    -p.c⟩⟩

@[simp] theorem mul_x0 (p q : T10) : (p * q).x0 =
    p.x0 + (q.x0 + p.a * q.x1 + p.b * q.x2) + p.s * (q.x3 + p.a * q.x4 + p.b * q.x5) := rfl
@[simp] theorem mul_x1 (p q : T10) : (p * q).x1 =
    p.x1 + (q.x1 + p.c * q.x2) + p.s * (q.x4 + p.c * q.x5) := rfl
@[simp] theorem mul_x2 (p q : T10) : (p * q).x2 = p.x2 + q.x2 + p.s * q.x5 := rfl
@[simp] theorem mul_x3 (p q : T10) : (p * q).x3 = p.x3 + (q.x3 + p.a * q.x4 + p.b * q.x5) := rfl
@[simp] theorem mul_x4 (p q : T10) : (p * q).x4 = p.x4 + (q.x4 + p.c * q.x5) := rfl
@[simp] theorem mul_x5 (p q : T10) : (p * q).x5 = p.x5 + q.x5 := rfl
@[simp] theorem mul_s (p q : T10) : (p * q).s = p.s + q.s := rfl
@[simp] theorem mul_a (p q : T10) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : T10) : (p * q).b = p.b + q.b + p.a * q.c := rfl
@[simp] theorem mul_c (p q : T10) : (p * q).c = p.c + q.c := rfl

@[simp] theorem one_x0 : (1 : T10).x0 = 0 := rfl
@[simp] theorem one_x1 : (1 : T10).x1 = 0 := rfl
@[simp] theorem one_x2 : (1 : T10).x2 = 0 := rfl
@[simp] theorem one_x3 : (1 : T10).x3 = 0 := rfl
@[simp] theorem one_x4 : (1 : T10).x4 = 0 := rfl
@[simp] theorem one_x5 : (1 : T10).x5 = 0 := rfl
@[simp] theorem one_s : (1 : T10).s = 0 := rfl
@[simp] theorem one_a : (1 : T10).a = 0 := rfl
@[simp] theorem one_b : (1 : T10).b = 0 := rfl
@[simp] theorem one_c : (1 : T10).c = 0 := rfl

@[simp] theorem inv_x0 (p : T10) : p⁻¹.x0 = -((p.x0 - p.a * p.x1 + (-p.b + p.a * p.c) * p.x2) -
    p.s * (p.x3 - p.a * p.x4 + (-p.b + p.a * p.c) * p.x5)) := rfl
@[simp] theorem inv_x1 (p : T10) :
    p⁻¹.x1 = -((p.x1 - p.c * p.x2) - p.s * (p.x4 - p.c * p.x5)) := rfl
@[simp] theorem inv_x2 (p : T10) : p⁻¹.x2 = -(p.x2 - p.s * p.x5) := rfl
@[simp] theorem inv_x3 (p : T10) :
    p⁻¹.x3 = -(p.x3 - p.a * p.x4 + (-p.b + p.a * p.c) * p.x5) := rfl
@[simp] theorem inv_x4 (p : T10) : p⁻¹.x4 = -(p.x4 - p.c * p.x5) := rfl
@[simp] theorem inv_x5 (p : T10) : p⁻¹.x5 = -p.x5 := rfl
@[simp] theorem inv_s (p : T10) : p⁻¹.s = -p.s := rfl
@[simp] theorem inv_a (p : T10) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : T10) : p⁻¹.b = -p.b + p.a * p.c := rfl
@[simp] theorem inv_c (p : T10) : p⁻¹.c = -p.c := rfl

instance : Group T10 where
  mul_assoc p q r := by
    ext <;> simp only [mul_x0, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_s, mul_a, mul_b,
      mul_c] <;> ring
  one_mul p := by
    ext <;> simp only [mul_x0, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_s, mul_a, mul_b, mul_c,
      one_x0, one_x1, one_x2, one_x3, one_x4, one_x5, one_s, one_a, one_b, one_c] <;> ring
  mul_one p := by
    ext <;> simp only [mul_x0, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_s, mul_a, mul_b, mul_c,
      one_x0, one_x1, one_x2, one_x3, one_x4, one_x5, one_s, one_a, one_b, one_c] <;> ring
  inv_mul_cancel p := by
    ext <;> simp only [mul_x0, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_s, mul_a, mul_b, mul_c,
      one_x0, one_x1, one_x2, one_x3, one_x4, one_x5, one_s, one_a, one_b, one_c, inv_x0, inv_x1,
      inv_x2, inv_x3, inv_x4, inv_x5, inv_s, inv_a, inv_b, inv_c] <;> ring

@[expose] def ofCode (n : ℕ) : T10 :=
  ⟨(n % 2 : ℕ), (n / 2 % 2 : ℕ), (n / 4 % 2 : ℕ), (n / 8 % 2 : ℕ), (n / 16 % 2 : ℕ),
    (n / 32 % 2 : ℕ), (n / 64 % 2 : ℕ), (n / 128 % 2 : ℕ), (n / 256 % 2 : ℕ), (n / 512 % 2 : ℕ)⟩

@[expose] def code10 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℕ) : ℕ :=
  v0 + 2 * v1 + 4 * v2 + 8 * v3 + 16 * v4 + 32 * v5 + 64 * v6 + 128 * v7 + 256 * v8 + 512 * v9

@[expose] def toCode (x : T10) : ℕ :=
  code10 x.x0.val x.x1.val x.x2.val x.x3.val x.x4.val x.x5.val x.s.val x.a.val x.b.val x.c.val

private theorem code10_digits {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℕ} (h0 : v0 < 2) (h1 : v1 < 2)
    (h2 : v2 < 2) (h3 : v3 < 2) (h4 : v4 < 2) (h5 : v5 < 2) (h6 : v6 < 2) (h7 : v7 < 2)
    (h8 : v8 < 2) (h9 : v9 < 2) :
    code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 < 1024 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 % 2 = v0 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 2 % 2 = v1 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 4 % 2 = v2 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 8 % 2 = v3 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 16 % 2 = v4 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 32 % 2 = v5 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 64 % 2 = v6 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 128 % 2 = v7 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 256 % 2 = v8 ∧
      code10 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 / 512 % 2 = v9 := by
  simp only [code10]
  omega

private theorem natCast_eq_of_val {n : ℕ} {z : ZMod 2} (h : n = z.val) : (n : ZMod 2) = z := by
  rw [h, ZMod.natCast_zmod_val]

theorem toCode_lt (x : T10) : toCode x < 1024 :=
  (code10_digits (ZMod.val_lt x.x0) (ZMod.val_lt x.x1) (ZMod.val_lt x.x2) (ZMod.val_lt x.x3)
    (ZMod.val_lt x.x4) (ZMod.val_lt x.x5) (ZMod.val_lt x.s) (ZMod.val_lt x.a) (ZMod.val_lt x.b)
    (ZMod.val_lt x.c)).1

theorem ofCode_toCode (x : T10) : ofCode (toCode x) = x := by
  obtain ⟨-, e0, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := code10_digits (ZMod.val_lt x.x0)
    (ZMod.val_lt x.x1) (ZMod.val_lt x.x2) (ZMod.val_lt x.x3) (ZMod.val_lt x.x4) (ZMod.val_lt x.x5)
    (ZMod.val_lt x.s) (ZMod.val_lt x.a) (ZMod.val_lt x.b) (ZMod.val_lt x.c)
  ext
  · exact natCast_eq_of_val e0
  · exact natCast_eq_of_val e1
  · exact natCast_eq_of_val e2
  · exact natCast_eq_of_val e3
  · exact natCast_eq_of_val e4
  · exact natCast_eq_of_val e5
  · exact natCast_eq_of_val e6
  · exact natCast_eq_of_val e7
  · exact natCast_eq_of_val e8
  · exact natCast_eq_of_val e9

theorem toCode_ofCode {n : ℕ} (hn : n < 1024) : toCode (ofCode n) = n := by
  show code10 (ZMod.val ((n % 2 : ℕ) : ZMod 2)) (ZMod.val ((n / 2 % 2 : ℕ) : ZMod 2))
    (ZMod.val ((n / 4 % 2 : ℕ) : ZMod 2)) (ZMod.val ((n / 8 % 2 : ℕ) : ZMod 2))
    (ZMod.val ((n / 16 % 2 : ℕ) : ZMod 2)) (ZMod.val ((n / 32 % 2 : ℕ) : ZMod 2))
    (ZMod.val ((n / 64 % 2 : ℕ) : ZMod 2)) (ZMod.val ((n / 128 % 2 : ℕ) : ZMod 2))
    (ZMod.val ((n / 256 % 2 : ℕ) : ZMod 2)) (ZMod.val ((n / 512 % 2 : ℕ) : ZMod 2)) = n
  rw [ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast,
    ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast,
    code10]
  omega

private theorem ofCode_inj {m n : ℕ} (hm : m < 1024) (hn : n < 1024) (h : ofCode m = ofCode n) :
    m = n := by
  rw [← toCode_ofCode hm, h, toCode_ofCode hn]

@[expose] def allL (_ : Unit := ()) : List T10 := (List.range 1024).map ofCode

theorem mem_allL (x : T10) : x ∈ allL () :=
  List.mem_map.2 ⟨toCode x, List.mem_range.2 (toCode_lt x), ofCode_toCode x⟩

theorem nodup_allL : (allL ()).Nodup :=
  List.Nodup.map_on (fun _ hm _ hn h => ofCode_inj (List.mem_range.1 hm) (List.mem_range.1 hn) h)
    List.nodup_range

instance : Fintype T10 := ⟨⟨allL (), nodup_allL⟩, mem_allL⟩

end T10

open T10

@[expose] def tm : T10 := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩

@[expose] def Qm : Subgroup T10 where
  carrier := {x | x.s = 0 ∧ x.a = 0 ∧ x.b = 0 ∧ x.c = 0}
  mul_mem' := by
    rintro p q ⟨hs, ha, hb, hc⟩ ⟨hs', ha', hb', hc'⟩
    simp [Set.mem_setOf_eq, mul_s, mul_a, mul_b, mul_c, hs, ha, hb, hc, hs', ha', hb', hc']
  one_mem' := by simp [Set.mem_setOf_eq, one_s, one_a, one_b, one_c]
  inv_mem' := by
    rintro p ⟨hs, ha, hb, hc⟩
    simp [Set.mem_setOf_eq, inv_s, inv_a, inv_b, inv_c, hs, ha, hb, hc]

@[expose] def Mm : Subgroup T10 where
  carrier := {x | x.s = 0}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq, mul_s] at hp hq ⊢
    rw [hp, hq, add_zero]
  one_mem' := by show (1 : T10).s = 0; rfl
  inv_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq, inv_s] at hp ⊢
    rw [hp, neg_zero]

@[expose] def inQ (x : T10) : Bool := x.s == 0 && x.a == 0 && x.b == 0 && x.c == 0

@[expose] def inM (x : T10) : Bool := x.s == 0

@[expose] def isInv (x : T10) : Bool := x * x == 1 && x != 1

@[expose] def commB (g x : T10) : Bool := g * x == x * g

@[expose] def repCodes : List ℕ :=
  [1, 2, 4, 8, 10, 12, 16, 17, 20, 32, 33, 34, 64, 128, 132, 160, 192, 256, 258, 272, 320, 512,
    513, 520, 576]

@[expose] def reps (_ : Unit := ()) : List T10 := repCodes.map ofCode

@[expose] def orbitOf (L : List T10) (r : T10) : List T10 := (L.map fun g => g * r * g⁻¹).dedup

@[expose] def clsIdx (O : List (List T10)) (x : T10) : ℕ := O.findIdx fun o => o.contains x

@[expose] def orbitsT (_ : Unit := ()) : List (List T10) :=
  let L := allL ()
  (reps ()).map (orbitOf L)

@[expose] def pairsT (_ : Unit := ()) : List (T10 × ℕ) :=
  let O := orbitsT ()
  ((allL ()).filter isInv).map fun x => (x, clsIdx O x)

@[expose] def members (P : List (T10 × ℕ)) (i : ℕ) : List T10 :=
  (P.filter fun p => p.2 == i).map Prod.fst

@[expose] def classesCommute (P : List (T10 × ℕ)) (i j : ℕ) : Bool :=
  let Ki := members P i
  let Kj := members P j
  Ki.all fun x => Kj.all fun y => commB x y

@[expose] def commTab (P : List (T10 × ℕ)) : Array (Array Bool) :=
  Array.ofFn (n := 25) fun i => Array.ofFn (n := 25) fun j => classesCommute P i j

@[expose] def cmOf (tab : Array (Array Bool)) (i j : ℕ) : Bool := (tab[i]?.getD #[])[j]?.getD false

@[expose] def cliques (cm : ℕ → ℕ → Bool) : List ℕ → List (List ℕ)
  | [] => [[]]
  | k :: ks =>
    let C := cliques cm ks
    C ++ (C.filter fun S => cm k k && S.all (cm k)).map (k :: ·)

@[expose] def leafOK (P : List (T10 × ℕ)) (S : List ℕ) : Bool :=
  let U := (P.filter fun p => S.contains p.2).map Prod.fst
  U.length != 63 || U.all inQ || (U.filter fun g => commB g tm).length == 15

@[expose] def t10CheckA (_ : Unit := ()) : Bool :=
  let P := pairsT ()
  let tab := commTab P
  P.all (fun p => decide (p.2 < 25)) && (cliques (cmOf tab) (List.range 25)).all (leafOK P)

@[expose] def t10CheckB (_ : Unit := ()) : Bool :=
  let L := allL ()
  L.all fun x => inQ x || !(x * x == 1) || inM x ||
    (L.filter fun g => inQ g && commB g x).length != 16

@[expose] def t10CheckC (_ : Unit := ()) : Bool :=
  let L := allL ()
  let cT := (L.filter fun g => commB g tm).length
  let iT := (L.filter fun g => commB g tm && isInv g).length
  cT == 128 && iT == 55 && L.all fun x => !inM x || inQ x || !isInv x ||
    (let cx := (L.filter fun g => commB g x).length
     let ix := (L.filter fun g => commB g x && isInv g).length
     !(cx == 256 || (cx == cT && ix == iT)) || L.any fun g => commB (g * x * g⁻¹) tm)

end CFSG.OddStandard.AltStdSmall4.ModT10
