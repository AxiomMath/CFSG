module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.OddStandard.AltStdSmall4.G2

open Matrix

namespace ModZ

variable {α : Type} [Group α] [DecidableEq α]

@[expose] def commB (g x : α) : Bool := g * x == x * g

@[expose] def checkE (L : List α) (inE : α → Bool) (N : ℕ) : Bool :=
  let S := L.map fun g => g * g
  L.all fun x => inE x == (x == 1 || (x * x == 1 && S.contains x &&
    decide (N ≤ (L.filter fun g => commB g x).length)))

@[expose] def conjCodes (LI : List (α × α)) (code : α → ℕ) (r : α) : List ℕ :=
  LI.map fun p => code (p.1 * r * p.2)

@[expose] def checkC (L : List α) (code : α → ℕ) (inM inA : α → Bool) (t : α) (N e : ℕ)
    (R : List α) : Bool :=
  let LI := L.map fun g => (g, g⁻¹)
  let O := R.map (conjCodes LI code)
  (R.all fun r =>
    (let C := L.filter fun g => commB g r
     C.length != N || C.any (fun y => y ^ e != 1) || LI.any fun p => commB (p.1 * r * p.2) t)) &&
  L.all fun x => !inM x || inA x || !(x * x == 1) || O.any fun o => o.contains (code x)

structure Ent (R : Type) where
  e00 : R
  e01 : R
  e02 : R
  e10 : R
  e11 : R
  e12 : R
  e20 : R
  e21 : R
  e22 : R

@[expose] def Ent.toMatrix {R : Type} (E : Ent R) : Matrix (Fin 3) (Fin 3) R :=
  !![E.e00, E.e01, E.e02; E.e10, E.e11, E.e12; E.e20, E.e21, E.e22]

end ModZ

@[ext] structure Z4M where
  x0 : ZMod 4
  x1 : ZMod 4
  x2 : ZMod 4
  s : ZMod 2
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
deriving DecidableEq

namespace Z4M

@[expose] def dEnt (a b c : ZMod 2) : ModZ.Ent (ZMod 4) :=
  if a = 0 then
    if b = 0 then
      if c = 0 then ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ else ⟨3, 0, 2, 0, 1, 3, 0, 0, 3⟩
    else
      if c = 0 then ⟨1, 0, 3, 0, 3, 0, 0, 0, 3⟩ else ⟨3, 0, 3, 0, 3, 1, 0, 0, 1⟩
  else
    if b = 0 then
      if c = 0 then ⟨3, 1, 2, 0, 1, 0, 0, 2, 3⟩ else ⟨1, 3, 0, 0, 3, 1, 0, 2, 1⟩
    else
      if c = 0 then ⟨3, 3, 3, 0, 3, 0, 0, 2, 1⟩ else ⟨1, 1, 3, 0, 1, 3, 0, 2, 3⟩

@[expose] def dMat (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 4) := (dEnt a b c).toMatrix

theorem dMat_mul : ∀ a b c a' b' c' : ZMod 2,
    dMat a b c * dMat a' b' c' = dMat (a + a') (b + b' + a * c') (c + c') := by
  decide

theorem dMat_zero : dMat 0 0 0 = 1 := by
  decide

@[expose] def uS (s : ZMod 2) : ZMod 4 := if s = 0 then 1 else -1

theorem uS_add : ∀ s s' : ZMod 2, uS (s + s') = uS s * uS s' := by
  decide

theorem uS_zero : uS 0 = 1 := if_pos rfl

instance : Mul Z4M := ⟨fun p q =>
  let M := dEnt p.a p.b p.c
  let w := uS p.s
  ⟨p.x0 + w * (M.e00 * q.x0 + M.e01 * q.x1 + M.e02 * q.x2),
    p.x1 + w * (M.e10 * q.x0 + M.e11 * q.x1 + M.e12 * q.x2),
    p.x2 + w * (M.e20 * q.x0 + M.e21 * q.x1 + M.e22 * q.x2),
    p.s + q.s, p.a + q.a, p.b + q.b + p.a * q.c, p.c + q.c⟩⟩

instance : One Z4M := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Inv Z4M := ⟨fun p =>
  let M := dEnt (-p.a) (-p.b + p.a * p.c) (-p.c)
  let w := uS (-p.s)
  ⟨-(w * (M.e00 * p.x0 + M.e01 * p.x1 + M.e02 * p.x2)),
    -(w * (M.e10 * p.x0 + M.e11 * p.x1 + M.e12 * p.x2)),
    -(w * (M.e20 * p.x0 + M.e21 * p.x1 + M.e22 * p.x2)),
    -p.s, -p.a, -p.b + p.a * p.c, -p.c⟩⟩

theorem mul_x0 (p q : Z4M) : (p * q).x0 = p.x0 + uS p.s * (dMat p.a p.b p.c 0 0 * q.x0 +
    dMat p.a p.b p.c 0 1 * q.x1 + dMat p.a p.b p.c 0 2 * q.x2) := rfl
theorem mul_x1 (p q : Z4M) : (p * q).x1 = p.x1 + uS p.s * (dMat p.a p.b p.c 1 0 * q.x0 +
    dMat p.a p.b p.c 1 1 * q.x1 + dMat p.a p.b p.c 1 2 * q.x2) := rfl
theorem mul_x2 (p q : Z4M) : (p * q).x2 = p.x2 + uS p.s * (dMat p.a p.b p.c 2 0 * q.x0 +
    dMat p.a p.b p.c 2 1 * q.x1 + dMat p.a p.b p.c 2 2 * q.x2) := rfl
@[simp] theorem mul_s (p q : Z4M) : (p * q).s = p.s + q.s := rfl
@[simp] theorem mul_a (p q : Z4M) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : Z4M) : (p * q).b = p.b + q.b + p.a * q.c := rfl
@[simp] theorem mul_c (p q : Z4M) : (p * q).c = p.c + q.c := rfl
@[simp] theorem one_x0 : (1 : Z4M).x0 = 0 := rfl
@[simp] theorem one_x1 : (1 : Z4M).x1 = 0 := rfl
@[simp] theorem one_x2 : (1 : Z4M).x2 = 0 := rfl
@[simp] theorem one_s : (1 : Z4M).s = 0 := rfl
@[simp] theorem one_a : (1 : Z4M).a = 0 := rfl
@[simp] theorem one_b : (1 : Z4M).b = 0 := rfl
@[simp] theorem one_c : (1 : Z4M).c = 0 := rfl
@[simp] theorem inv_s (p : Z4M) : p⁻¹.s = -p.s := rfl
@[simp] theorem inv_a (p : Z4M) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : Z4M) : p⁻¹.b = -p.b + p.a * p.c := rfl
@[simp] theorem inv_c (p : Z4M) : p⁻¹.c = -p.c := rfl
theorem inv_x0 (p : Z4M) : p⁻¹.x0 = -(uS p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 2 * p.x2)) := rfl
theorem inv_x1 (p : Z4M) : p⁻¹.x1 = -(uS p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 2 * p.x2)) := rfl
theorem inv_x2 (p : Z4M) : p⁻¹.x2 = -(uS p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 2 * p.x2)) := rfl

@[expose] def vec (p : Z4M) : Fin 3 → ZMod 4 := ![p.x0, p.x1, p.x2]

theorem vec_mul (p q : Z4M) : vec (p * q) = vec p + uS p.s • (dMat p.a p.b p.c *ᵥ vec q) := by
  funext i
  fin_cases i <;> simp [vec, mul_x0, mul_x1, mul_x2, mulVec, dotProduct, Fin.sum_univ_three]

theorem vec_inv (p : Z4M) :
    vec p⁻¹ = -(uS p⁻¹.s • (dMat p⁻¹.a p⁻¹.b p⁻¹.c *ᵥ vec p)) := by
  funext i
  fin_cases i <;> simp only [vec, inv_x0, inv_x1, inv_x2, mulVec, dotProduct, Fin.sum_univ_three,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem vec_one : vec 1 = 0 := by
  funext i
  fin_cases i <;> rfl

theorem ext_vec {p q : Z4M} (hv : vec p = vec q) (hs : p.s = q.s) (ha : p.a = q.a)
    (hb : p.b = q.b) (hc : p.c = q.c) : p = q :=
  Z4M.ext (congrFun hv 0) (congrFun hv 1) (congrFun hv 2) hs ha hb hc

instance : Group Z4M where
  mul_assoc p q r := by
    refine ext_vec ?_ (by simp only [mul_s]; ring) (by simp only [mul_a]; ring)
      (by simp only [mul_a, mul_b, mul_c]; ring) (by simp only [mul_c]; ring)
    simp only [vec_mul, mul_s, mul_a, mul_b, mul_c]
    rw [← dMat_mul, uS_add, mulVec_add, smul_add, mulVec_smul, smul_smul, mulVec_mulVec,
      add_assoc]
  one_mul p := by
    refine ext_vec ?_ (by simp only [mul_s, one_s]; ring) (by simp only [mul_a, one_a]; ring)
      (by simp only [mul_b, one_a, one_b]; ring) (by simp only [mul_c, one_c]; ring)
    rw [vec_mul, vec_one, one_s, one_a, one_b, one_c, uS_zero, dMat_zero, one_mulVec, one_smul,
      zero_add]
  mul_one p := by
    refine ext_vec ?_ (by simp only [mul_s, one_s]; ring) (by simp only [mul_a, one_a]; ring)
      (by simp only [mul_b, one_b, one_c]; ring) (by simp only [mul_c, one_c]; ring)
    rw [vec_mul, vec_one, mulVec_zero, smul_zero, add_zero]
  inv_mul_cancel p := by
    refine ext_vec ?_ (by simp only [mul_s, inv_s, one_s]; ring)
      (by simp only [mul_a, inv_a, one_a]; ring)
      (by simp only [mul_b, inv_a, inv_b, one_b]; ring) (by simp only [mul_c, inv_c, one_c]; ring)
    rw [vec_mul, vec_inv, vec_one, neg_add_cancel]

@[expose] def ofCode (n : ℕ) : Z4M :=
  ⟨(n % 4 : ℕ), (n / 4 % 4 : ℕ), (n / 16 % 4 : ℕ), (n / 64 % 2 : ℕ), (n / 128 % 2 : ℕ),
    (n / 256 % 2 : ℕ), (n / 512 % 2 : ℕ)⟩

@[expose] def toCode (p : Z4M) : ℕ :=
  p.x0.val + 4 * p.x1.val + 16 * p.x2.val + 64 * p.s.val + 128 * p.a.val + 256 * p.b.val +
    512 * p.c.val

private theorem code_digits {v0 v1 v2 v3 v4 v5 v6 : ℕ} (h0 : v0 < 4) (h1 : v1 < 4) (h2 : v2 < 4)
    (h3 : v3 < 2) (h4 : v4 < 2) (h5 : v5 < 2) (h6 : v6 < 2) :
    v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6 < 1024 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) % 4 = v0 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 4 % 4 = v1 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 16 % 4 = v2 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 64 % 2 = v3 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 128 % 2 = v4 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 256 % 2 = v5 ∧
      (v0 + 4 * v1 + 16 * v2 + 64 * v3 + 128 * v4 + 256 * v5 + 512 * v6) / 512 % 2 = v6 := by
  omega

private theorem natCast_eq_of_val {m : ℕ} [NeZero m] {n : ℕ} {z : ZMod m} (h : n = z.val) :
    (n : ZMod m) = z := by
  rw [h, ZMod.natCast_zmod_val]

theorem toCode_lt (p : Z4M) : toCode p < 1024 :=
  (code_digits (ZMod.val_lt p.x0) (ZMod.val_lt p.x1) (ZMod.val_lt p.x2) (ZMod.val_lt p.s)
    (ZMod.val_lt p.a) (ZMod.val_lt p.b) (ZMod.val_lt p.c)).1

theorem ofCode_toCode (p : Z4M) : ofCode (toCode p) = p := by
  obtain ⟨-, e0, e1, e2, e3, e4, e5, e6⟩ := code_digits (ZMod.val_lt p.x0) (ZMod.val_lt p.x1)
    (ZMod.val_lt p.x2) (ZMod.val_lt p.s) (ZMod.val_lt p.a) (ZMod.val_lt p.b) (ZMod.val_lt p.c)
  ext
  · exact natCast_eq_of_val e0
  · exact natCast_eq_of_val e1
  · exact natCast_eq_of_val e2
  · exact natCast_eq_of_val e3
  · exact natCast_eq_of_val e4
  · exact natCast_eq_of_val e5
  · exact natCast_eq_of_val e6

theorem toCode_ofCode {n : ℕ} (hn : n < 1024) : toCode (ofCode n) = n := by
  show ZMod.val ((n % 4 : ℕ) : ZMod 4) + 4 * ZMod.val ((n / 4 % 4 : ℕ) : ZMod 4) +
    16 * ZMod.val ((n / 16 % 4 : ℕ) : ZMod 4) + 64 * ZMod.val ((n / 64 % 2 : ℕ) : ZMod 2) +
    128 * ZMod.val ((n / 128 % 2 : ℕ) : ZMod 2) + 256 * ZMod.val ((n / 256 % 2 : ℕ) : ZMod 2) +
    512 * ZMod.val ((n / 512 % 2 : ℕ) : ZMod 2) = n
  simp only [ZMod.val_natCast]
  omega

@[expose] def allL (_ : Unit := ()) : List Z4M := (List.range 1024).map ofCode

theorem mem_allL (p : Z4M) : p ∈ allL () :=
  List.mem_map.2 ⟨toCode p, List.mem_range.2 (toCode_lt p), ofCode_toCode p⟩

theorem nodup_allL : (allL ()).Nodup :=
  List.Nodup.map_on (fun _ hm _ hn h => by
    rw [← toCode_ofCode (List.mem_range.1 hm), h, toCode_ofCode (List.mem_range.1 hn)])
    List.nodup_range

instance : Fintype Z4M := ⟨⟨allL (), nodup_allL⟩, mem_allL⟩

@[expose] def tm : Z4M := ⟨0, 0, 0, 1, 0, 0, 0⟩

@[expose] def Am : Subgroup Z4M where
  carrier := {p | p.s = 0 ∧ p.a = 0 ∧ p.b = 0 ∧ p.c = 0}
  mul_mem' := by
    rintro p q ⟨hs, ha, hb, hc⟩ ⟨hs', ha', hb', hc'⟩
    simp [hs, ha, hb, hc, hs', ha', hb', hc']
  one_mem' := by simp
  inv_mem' := by
    rintro p ⟨hs, ha, hb, hc⟩
    simp [hs, ha, hb, hc]

@[expose] def Mm : Subgroup Z4M where
  carrier := {p | p.s = 0}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq, mul_s] at hp hq ⊢
    rw [hp, hq, add_zero]
  one_mem' := by
    show (0 : ZMod 2) = 0
    rfl
  inv_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq, inv_s] at hp ⊢
    rw [hp, neg_zero]

theorem vec_mul_of_mem_Am {p : Z4M} (hp : p ∈ Am) (q : Z4M) : vec (p * q) = vec p + vec q := by
  obtain ⟨hs, ha, hb, hc⟩ := hp
  rw [vec_mul, hs, ha, hb, hc, uS_zero, dMat_zero, one_mulVec, one_smul]

@[expose] def Em : Subgroup Z4M where
  carrier := {p | p ∈ Am ∧ 2 * p.x0 = 0 ∧ 2 * p.x1 = 0 ∧ 2 * p.x2 = 0}
  mul_mem' := by
    rintro p q ⟨hp, h0, h1, h2⟩ ⟨hq, h0', h1', h2'⟩
    have hv := vec_mul_of_mem_Am hp q
    have e0 : (p * q).x0 = p.x0 + q.x0 := congrFun hv 0
    have e1 : (p * q).x1 = p.x1 + q.x1 := congrFun hv 1
    have e2 : (p * q).x2 = p.x2 + q.x2 := congrFun hv 2
    refine ⟨Am.mul_mem hp hq, ?_, ?_, ?_⟩
    · rw [e0, mul_add, h0, h0', add_zero]
    · rw [e1, mul_add, h1, h1', add_zero]
    · rw [e2, mul_add, h2, h2', add_zero]
  one_mem' := ⟨Am.one_mem, mul_zero _, mul_zero _, mul_zero _⟩
  inv_mem' := by
    rintro p ⟨hp, h0, h1, h2⟩
    have hv := vec_mul_of_mem_Am (Am.inv_mem hp) p
    rw [inv_mul_cancel, vec_one] at hv
    have e0 : p⁻¹.x0 = -p.x0 := eq_neg_of_add_eq_zero_left (congrFun hv 0).symm
    have e1 : p⁻¹.x1 = -p.x1 := eq_neg_of_add_eq_zero_left (congrFun hv 1).symm
    have e2 : p⁻¹.x2 = -p.x2 := eq_neg_of_add_eq_zero_left (congrFun hv 2).symm
    refine ⟨Am.inv_mem hp, ?_, ?_, ?_⟩
    · rw [e0, mul_neg, h0, neg_zero]
    · rw [e1, mul_neg, h1, neg_zero]
    · rw [e2, mul_neg, h2, neg_zero]

@[expose] def inA (p : Z4M) : Bool := p.s == 0 && p.a == 0 && p.b == 0 && p.c == 0

@[expose] def inM (p : Z4M) : Bool := p.s == 0

@[expose] def inE (p : Z4M) : Bool :=
  inA p && 2 * p.x0 == 0 && 2 * p.x1 == 0 && 2 * p.x2 == 0

@[expose] def reps (_ : Unit := ()) : List Z4M := [128, 152, 256, 260, 512, 513].map ofCode

end Z4M

@[ext] structure Z8M (u : (ZMod 8)ˣ) where
  x0 : ZMod 8
  x1 : ZMod 8
  x2 : ZMod 8
  s : ZMod 2
  a : ZMod 2
  b : ZMod 2
  c : ZMod 2
deriving DecidableEq

namespace Z8M

@[expose] def uThree : (ZMod 8)ˣ := ⟨3, 3, rfl, rfl⟩

@[expose] def dEnt (a b c : ZMod 2) : ModZ.Ent (ZMod 8) :=
  if a = 0 then
    if b = 0 then
      if c = 0 then ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ else ⟨7, 4, 6, 0, 5, 3, 0, 0, 3⟩
    else
      if c = 0 then ⟨1, 0, 3, 0, 7, 4, 0, 0, 7⟩ else ⟨7, 4, 7, 0, 3, 1, 0, 0, 5⟩
  else
    if b = 0 then
      if c = 0 then ⟨3, 1, 6, 0, 1, 4, 0, 2, 3⟩ else ⟨5, 7, 4, 0, 3, 5, 0, 6, 1⟩
    else
      if c = 0 then ⟨3, 7, 7, 0, 7, 0, 0, 6, 5⟩ else ⟨5, 1, 7, 0, 5, 7, 0, 2, 7⟩

@[expose] def dMat (a b c : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 8) := (dEnt a b c).toMatrix

theorem dMat_mul : ∀ a b c a' b' c' : ZMod 2,
    dMat a b c * dMat a' b' c' = dMat (a + a') (b + b' + a * c') (c + c') := by
  decide

theorem dMat_zero : dMat 0 0 0 = 1 := by
  decide

theorem val_mul_self (u : (ZMod 8)ˣ) : (u : ZMod 8) * u = 1 := by
  have h : ∀ x y : ZMod 8, x * y = 1 → x * x = 1 := by decide
  exact h _ _ u.mul_inv

variable {u : (ZMod 8)ˣ}

@[expose] def uS (u : (ZMod 8)ˣ) (s : ZMod 2) : ZMod 8 := if s = 0 then 1 else (u : ZMod 8)

theorem uS_zero (u : (ZMod 8)ˣ) : uS u 0 = 1 := if_pos rfl

theorem uS_add (u : (ZMod 8)ˣ) (s s' : ZMod 2) : uS u (s + s') = uS u s * uS u s' := by
  have hc : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have h1 : uS u 1 = u := if_neg (by decide)
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hc s with rfl | rfl <;> rcases hc s' with rfl | rfl
  · rw [add_zero, uS_zero, mul_one]
  · rw [zero_add, uS_zero, one_mul]
  · rw [add_zero, uS_zero, mul_one]
  · rw [h11, uS_zero, h1, val_mul_self]

instance : Mul (Z8M u) := ⟨fun p q =>
  let M := dEnt p.a p.b p.c
  let w := uS u p.s
  ⟨p.x0 + w * (M.e00 * q.x0 + M.e01 * q.x1 + M.e02 * q.x2),
    p.x1 + w * (M.e10 * q.x0 + M.e11 * q.x1 + M.e12 * q.x2),
    p.x2 + w * (M.e20 * q.x0 + M.e21 * q.x1 + M.e22 * q.x2),
    p.s + q.s, p.a + q.a, p.b + q.b + p.a * q.c, p.c + q.c⟩⟩

instance : One (Z8M u) := ⟨⟨0, 0, 0, 0, 0, 0, 0⟩⟩

instance : Inv (Z8M u) := ⟨fun p =>
  let M := dEnt (-p.a) (-p.b + p.a * p.c) (-p.c)
  let w := uS u (-p.s)
  ⟨-(w * (M.e00 * p.x0 + M.e01 * p.x1 + M.e02 * p.x2)),
    -(w * (M.e10 * p.x0 + M.e11 * p.x1 + M.e12 * p.x2)),
    -(w * (M.e20 * p.x0 + M.e21 * p.x1 + M.e22 * p.x2)),
    -p.s, -p.a, -p.b + p.a * p.c, -p.c⟩⟩

theorem mul_x0 (p q : Z8M u) : (p * q).x0 = p.x0 + uS u p.s * (dMat p.a p.b p.c 0 0 * q.x0 +
    dMat p.a p.b p.c 0 1 * q.x1 + dMat p.a p.b p.c 0 2 * q.x2) := rfl
theorem mul_x1 (p q : Z8M u) : (p * q).x1 = p.x1 + uS u p.s * (dMat p.a p.b p.c 1 0 * q.x0 +
    dMat p.a p.b p.c 1 1 * q.x1 + dMat p.a p.b p.c 1 2 * q.x2) := rfl
theorem mul_x2 (p q : Z8M u) : (p * q).x2 = p.x2 + uS u p.s * (dMat p.a p.b p.c 2 0 * q.x0 +
    dMat p.a p.b p.c 2 1 * q.x1 + dMat p.a p.b p.c 2 2 * q.x2) := rfl
@[simp] theorem mul_s (p q : Z8M u) : (p * q).s = p.s + q.s := rfl
@[simp] theorem mul_a (p q : Z8M u) : (p * q).a = p.a + q.a := rfl
@[simp] theorem mul_b (p q : Z8M u) : (p * q).b = p.b + q.b + p.a * q.c := rfl
@[simp] theorem mul_c (p q : Z8M u) : (p * q).c = p.c + q.c := rfl
@[simp] theorem one_x0 : (1 : Z8M u).x0 = 0 := rfl
@[simp] theorem one_x1 : (1 : Z8M u).x1 = 0 := rfl
@[simp] theorem one_x2 : (1 : Z8M u).x2 = 0 := rfl
@[simp] theorem one_s : (1 : Z8M u).s = 0 := rfl
@[simp] theorem one_a : (1 : Z8M u).a = 0 := rfl
@[simp] theorem one_b : (1 : Z8M u).b = 0 := rfl
@[simp] theorem one_c : (1 : Z8M u).c = 0 := rfl
@[simp] theorem inv_s (p : Z8M u) : p⁻¹.s = -p.s := rfl
@[simp] theorem inv_a (p : Z8M u) : p⁻¹.a = -p.a := rfl
@[simp] theorem inv_b (p : Z8M u) : p⁻¹.b = -p.b + p.a * p.c := rfl
@[simp] theorem inv_c (p : Z8M u) : p⁻¹.c = -p.c := rfl
theorem inv_x0 (p : Z8M u) : p⁻¹.x0 = -(uS u p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 0 2 * p.x2)) := rfl
theorem inv_x1 (p : Z8M u) : p⁻¹.x1 = -(uS u p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 1 2 * p.x2)) := rfl
theorem inv_x2 (p : Z8M u) : p⁻¹.x2 = -(uS u p⁻¹.s * (dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 0 * p.x0 +
    dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 1 * p.x1 + dMat p⁻¹.a p⁻¹.b p⁻¹.c 2 2 * p.x2)) := rfl

@[expose] def vec (p : Z8M u) : Fin 3 → ZMod 8 := ![p.x0, p.x1, p.x2]

theorem vec_mul (p q : Z8M u) :
    vec (p * q) = vec p + uS u p.s • (dMat p.a p.b p.c *ᵥ vec q) := by
  funext i
  fin_cases i <;> simp [vec, mul_x0, mul_x1, mul_x2, mulVec, dotProduct, Fin.sum_univ_three]

theorem vec_inv (p : Z8M u) :
    vec p⁻¹ = -(uS u p⁻¹.s • (dMat p⁻¹.a p⁻¹.b p⁻¹.c *ᵥ vec p)) := by
  funext i
  fin_cases i <;> simp only [vec, inv_x0, inv_x1, inv_x2, mulVec, dotProduct, Fin.sum_univ_three,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]

theorem vec_one : vec (1 : Z8M u) = 0 := by
  funext i
  fin_cases i <;> rfl

theorem ext_vec {p q : Z8M u} (hv : vec p = vec q) (hs : p.s = q.s) (ha : p.a = q.a)
    (hb : p.b = q.b) (hc : p.c = q.c) : p = q :=
  Z8M.ext (congrFun hv 0) (congrFun hv 1) (congrFun hv 2) hs ha hb hc

instance : Group (Z8M u) where
  mul_assoc p q r := by
    refine ext_vec ?_ (by simp only [mul_s]; ring) (by simp only [mul_a]; ring)
      (by simp only [mul_a, mul_b, mul_c]; ring) (by simp only [mul_c]; ring)
    simp only [vec_mul, mul_s, mul_a, mul_b, mul_c]
    rw [← dMat_mul, uS_add, mulVec_add, smul_add, mulVec_smul, smul_smul, mulVec_mulVec,
      add_assoc]
  one_mul p := by
    refine ext_vec ?_ (by simp only [mul_s, one_s]; ring) (by simp only [mul_a, one_a]; ring)
      (by simp only [mul_b, one_a, one_b]; ring) (by simp only [mul_c, one_c]; ring)
    rw [vec_mul, vec_one, one_s, one_a, one_b, one_c, uS_zero, dMat_zero, one_mulVec, one_smul,
      zero_add]
  mul_one p := by
    refine ext_vec ?_ (by simp only [mul_s, one_s]; ring) (by simp only [mul_a, one_a]; ring)
      (by simp only [mul_b, one_b, one_c]; ring) (by simp only [mul_c, one_c]; ring)
    rw [vec_mul, vec_one, mulVec_zero, smul_zero, add_zero]
  inv_mul_cancel p := by
    refine ext_vec ?_ (by simp only [mul_s, inv_s, one_s]; ring)
      (by simp only [mul_a, inv_a, one_a]; ring)
      (by simp only [mul_b, inv_a, inv_b, one_b]; ring) (by simp only [mul_c, inv_c, one_c]; ring)
    rw [vec_mul, vec_inv, vec_one, neg_add_cancel]

@[expose] def ofCode (u : (ZMod 8)ˣ) (n : ℕ) : Z8M u :=
  ⟨(n % 8 : ℕ), (n / 8 % 8 : ℕ), (n / 64 % 8 : ℕ), (n / 512 % 2 : ℕ), (n / 1024 % 2 : ℕ),
    (n / 2048 % 2 : ℕ), (n / 4096 % 2 : ℕ)⟩

@[expose] def toCode (p : Z8M u) : ℕ :=
  p.x0.val + 8 * p.x1.val + 64 * p.x2.val + 512 * p.s.val + 1024 * p.a.val + 2048 * p.b.val +
    4096 * p.c.val

private theorem code_digits {v0 v1 v2 v3 v4 v5 v6 : ℕ} (h0 : v0 < 8) (h1 : v1 < 8) (h2 : v2 < 8)
    (h3 : v3 < 2) (h4 : v4 < 2) (h5 : v5 < 2) (h6 : v6 < 2) :
    v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6 < 8192 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) % 8 = v0 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 8 % 8 = v1 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 64 % 8 = v2 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 512 % 2 = v3 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 1024 % 2 = v4 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 2048 % 2 = v5 ∧
      (v0 + 8 * v1 + 64 * v2 + 512 * v3 + 1024 * v4 + 2048 * v5 + 4096 * v6) / 4096 % 2 = v6 := by
  omega

private theorem natCast_eq_of_val {m : ℕ} [NeZero m] {n : ℕ} {z : ZMod m} (h : n = z.val) :
    (n : ZMod m) = z := by
  rw [h, ZMod.natCast_zmod_val]

theorem toCode_lt (p : Z8M u) : toCode p < 8192 :=
  (code_digits (ZMod.val_lt p.x0) (ZMod.val_lt p.x1) (ZMod.val_lt p.x2) (ZMod.val_lt p.s)
    (ZMod.val_lt p.a) (ZMod.val_lt p.b) (ZMod.val_lt p.c)).1

theorem ofCode_toCode (p : Z8M u) : ofCode u (toCode p) = p := by
  obtain ⟨-, e0, e1, e2, e3, e4, e5, e6⟩ := code_digits (ZMod.val_lt p.x0) (ZMod.val_lt p.x1)
    (ZMod.val_lt p.x2) (ZMod.val_lt p.s) (ZMod.val_lt p.a) (ZMod.val_lt p.b) (ZMod.val_lt p.c)
  ext
  · exact natCast_eq_of_val e0
  · exact natCast_eq_of_val e1
  · exact natCast_eq_of_val e2
  · exact natCast_eq_of_val e3
  · exact natCast_eq_of_val e4
  · exact natCast_eq_of_val e5
  · exact natCast_eq_of_val e6

theorem toCode_ofCode {n : ℕ} (hn : n < 8192) : toCode (ofCode u n) = n := by
  show ZMod.val ((n % 8 : ℕ) : ZMod 8) + 8 * ZMod.val ((n / 8 % 8 : ℕ) : ZMod 8) +
    64 * ZMod.val ((n / 64 % 8 : ℕ) : ZMod 8) + 512 * ZMod.val ((n / 512 % 2 : ℕ) : ZMod 2) +
    1024 * ZMod.val ((n / 1024 % 2 : ℕ) : ZMod 2) +
    2048 * ZMod.val ((n / 2048 % 2 : ℕ) : ZMod 2) +
    4096 * ZMod.val ((n / 4096 % 2 : ℕ) : ZMod 2) = n
  simp only [ZMod.val_natCast]
  omega

@[expose] def allL (u : (ZMod 8)ˣ) (_ : Unit := ()) : List (Z8M u) :=
  (List.range 8192).map (ofCode u)

theorem mem_allL (p : Z8M u) : p ∈ allL u () :=
  List.mem_map.2 ⟨toCode p, List.mem_range.2 (toCode_lt p), ofCode_toCode p⟩

theorem nodup_allL : (allL u ()).Nodup :=
  List.Nodup.map_on (fun _ hm _ hn h => by
    rw [← toCode_ofCode (u := u) (List.mem_range.1 hm), h,
      toCode_ofCode (List.mem_range.1 hn)])
    List.nodup_range

instance : Fintype (Z8M u) := ⟨⟨allL u (), nodup_allL⟩, mem_allL⟩

@[expose] def tm (u : (ZMod 8)ˣ) : Z8M u := ⟨0, 0, 0, 1, 0, 0, 0⟩

@[expose] def Am (u : (ZMod 8)ˣ) : Subgroup (Z8M u) where
  carrier := {p | p.s = 0 ∧ p.a = 0 ∧ p.b = 0 ∧ p.c = 0}
  mul_mem' := by
    rintro p q ⟨hs, ha, hb, hc⟩ ⟨hs', ha', hb', hc'⟩
    simp [hs, ha, hb, hc, hs', ha', hb', hc']
  one_mem' := by simp
  inv_mem' := by
    rintro p ⟨hs, ha, hb, hc⟩
    simp [hs, ha, hb, hc]

@[expose] def Mm (u : (ZMod 8)ˣ) : Subgroup (Z8M u) where
  carrier := {p | p.s = 0}
  mul_mem' := by
    intro p q hp hq
    simp only [Set.mem_setOf_eq, mul_s] at hp hq ⊢
    rw [hp, hq, add_zero]
  one_mem' := by
    show (0 : ZMod 2) = 0
    rfl
  inv_mem' := by
    intro p hp
    simp only [Set.mem_setOf_eq, inv_s] at hp ⊢
    rw [hp, neg_zero]

theorem vec_mul_of_mem_Am {p : Z8M u} (hp : p ∈ Am u) (q : Z8M u) :
    vec (p * q) = vec p + vec q := by
  obtain ⟨hs, ha, hb, hc⟩ := hp
  rw [vec_mul, hs, ha, hb, hc, uS_zero, dMat_zero, one_mulVec, one_smul]

@[expose] def Em (u : (ZMod 8)ˣ) : Subgroup (Z8M u) where
  carrier := {p | p ∈ Am u ∧ 2 * p.x0 = 0 ∧ 2 * p.x1 = 0 ∧ 2 * p.x2 = 0}
  mul_mem' := by
    rintro p q ⟨hp, h0, h1, h2⟩ ⟨hq, h0', h1', h2'⟩
    have hv := vec_mul_of_mem_Am hp q
    have e0 : (p * q).x0 = p.x0 + q.x0 := congrFun hv 0
    have e1 : (p * q).x1 = p.x1 + q.x1 := congrFun hv 1
    have e2 : (p * q).x2 = p.x2 + q.x2 := congrFun hv 2
    refine ⟨(Am u).mul_mem hp hq, ?_, ?_, ?_⟩
    · rw [e0, mul_add, h0, h0', add_zero]
    · rw [e1, mul_add, h1, h1', add_zero]
    · rw [e2, mul_add, h2, h2', add_zero]
  one_mem' := ⟨(Am u).one_mem, mul_zero _, mul_zero _, mul_zero _⟩
  inv_mem' := by
    rintro p ⟨hp, h0, h1, h2⟩
    have hv := vec_mul_of_mem_Am ((Am u).inv_mem hp) p
    rw [inv_mul_cancel, vec_one] at hv
    have e0 : p⁻¹.x0 = -p.x0 := eq_neg_of_add_eq_zero_left (congrFun hv 0).symm
    have e1 : p⁻¹.x1 = -p.x1 := eq_neg_of_add_eq_zero_left (congrFun hv 1).symm
    have e2 : p⁻¹.x2 = -p.x2 := eq_neg_of_add_eq_zero_left (congrFun hv 2).symm
    refine ⟨(Am u).inv_mem hp, ?_, ?_, ?_⟩
    · rw [e0, mul_neg, h0, neg_zero]
    · rw [e1, mul_neg, h1, neg_zero]
    · rw [e2, mul_neg, h2, neg_zero]

@[expose] def inA (p : Z8M u) : Bool := p.s == 0 && p.a == 0 && p.b == 0 && p.c == 0

@[expose] def inM (p : Z8M u) : Bool := p.s == 0

@[expose] def inE (p : Z8M u) : Bool :=
  inA p && 2 * p.x0 == 0 && 2 * p.x1 == 0 && 2 * p.x2 == 0

@[expose] def reps (u : (ZMod 8)ˣ) (_ : Unit := ()) : List (Z8M u) :=
  [1024, 1104, 2048, 2056, 4096, 4097].map (ofCode u)

end Z8M

@[expose] def z4CheckE (_ : Unit := ()) : Bool := ModZ.checkE (Z4M.allL ()) Z4M.inE (2 ^ 8)

@[expose] def z4CheckC (_ : Unit := ()) : Bool :=
  let L := Z4M.allL ()
  let R := Z4M.reps ()
  ModZ.checkC L Z4M.toCode Z4M.inM Z4M.inA Z4M.tm (2 ^ 7) 4 R &&
    ModZ.checkC L Z4M.toCode Z4M.inM Z4M.inA Z4M.tm (2 ^ 8) 8 R

@[expose] def z8CheckC (u : (ZMod 8)ˣ) (_ : Unit := ()) : Bool :=
  ModZ.checkC (Z8M.allL u ()) Z8M.toCode Z8M.inM Z8M.inA (Z8M.tm u) (2 ^ 8) 8 (Z8M.reps u ())

end CFSG.OddStandard.AltStdSmall4.G2
