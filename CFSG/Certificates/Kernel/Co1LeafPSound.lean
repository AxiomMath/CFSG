module

public import Certificates.Data.Kernel.Co1LeafP
import CFSG.Certificates.Kernel.F2WordSound
public import Aesop.BuiltinRules
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Tactic.ToAdditive
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.Co1LeafP

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1BBound

structure Equi (XB : Nat → Nat) (BT : List Nat) (f : Nat → Nat) : Prop where
  lt : ∀ x, x < 2 ^ 24 → f x < 2 ^ 24
  add : ∀ x y, x < 2 ^ 24 → y < 2 ^ 24 → f (x ^^^ y) = f x ^^^ f y
  comm : ∀ s, s < BT.length → ∀ x, x < 2 ^ 24 →
    f (vmF 24 (BT.getD s 0) x) = vmF 24 (BT.getD s 0) (f x)
  mem : ∀ x, x < 2 ^ 24 → memK XB (f x) = memK XB x

section Lemmas

open CFSG.KC.Co1Leaf (selK crdK strictL)
open CFSG.KLie.CT (andB allN pw2 fget maskN)

theorem lp_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact absurd h Bool.false_ne_true

theorem lp_strictB (y : ℕ) (k : ℕ → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem lp_strictL (y : ℕ) (k : ℕ → List ℕ) : strictL y k = k y := by
  cases y <;> rfl

theorem lp_allN {f : ℕ → Bool} : ∀ {n : ℕ}, allN n f = true → ∀ k < n, f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := lp_andB h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact lp_allN h2 k hk
    · exact h1

theorem lp_pw2 (w : ℕ) : pw2 w = 2 ^ w := Nat.one_shiftLeft w

theorem lp_lenL : ∀ L : List ℕ, lenL L = L.length
  | [] => rfl
  | _ :: L => congrArg Nat.succ (lp_lenL L)

theorem lp_getL (x : ℕ) : ∀ (L : List ℕ) (i : ℕ), getL x L i = L.getD i x
  | [], _ => by rw [List.getD_nil]; all_goals rfl
  | a :: L, 0 => by rw [List.getD_cons_zero]; all_goals rfl
  | a :: L, i + 1 => by rw [List.getD_cons_succ]; exact lp_getL x L i

theorem lp_getLP : ∀ (L : List (List ℕ)) (i : ℕ), getLP L i = L.getD i []
  | [], _ => by rw [List.getD_nil]; all_goals rfl
  | a :: L, 0 => by rw [List.getD_cons_zero]; all_goals rfl
  | a :: L, i + 1 => by rw [List.getD_cons_succ]; exact lp_getLP L i

theorem lp_xor4 (a b c e : ℕ) : (a ^^^ b) ^^^ (c ^^^ e) = (a ^^^ c) ^^^ (b ^^^ e) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> cases c.testBit j <;> cases e.testBit j <;> rfl

theorem lp_x1 (x a b : ℕ) : a ^^^ b = (x ^^^ a) ^^^ (x ^^^ b) := by
  rw [lp_xor4, Nat.xor_self, Nat.zero_xor]

theorem lp_x2 (x a b : ℕ) : x ^^^ (a ^^^ b) = (x ^^^ a) ^^^ b := (Nat.xor_assoc x a b).symm

theorem lp_x3 (x a b : ℕ) : x ^^^ (a ^^^ b) = a ^^^ (x ^^^ b) := by
  rw [← Nat.xor_assoc, Nat.xor_comm x a, Nat.xor_assoc]

theorem lp_rec_succ {z : ℕ} {s : ℕ → ℕ → ℕ} (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) z s (n + 1) = s n (Nat.rec (motive := fun _ => ℕ) z s n) := rfl

theorem lp_xor_lt {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) : a ^^^ b < 2 ^ 24 :=
  Nat.xor_lt_two_pow ha hb

theorem lp_shr_xor (a b : ℕ) : (a ^^^ b) >>> 1 = (a >>> 1) ^^^ (b >>> 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_shiftRight, Nat.testBit_xor]

theorem lp_bit0 (a : ℕ) : Nat.beq (Nat.land a 1) 1 = a.testBit 0 := by
  have e : Nat.land a 1 = a % 2 := Nat.and_one_is_mod a
  rw [e, Nat.testBit_eq_decide_div_mod_eq, pow_zero, Nat.div_one]
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;> (rw [h]; all_goals rfl)

theorem lp_selK_t {x : ℕ} {L : List ℕ} {a : ℕ} (h : a.testBit 0 = true) :
    selK (x :: L) a = x ^^^ selK L (a >>> 1) := by
  change Bool.rec (motive := fun _ => ℕ) (selK L (Nat.shiftRight a 1))
    (Nat.xor x (selK L (Nat.shiftRight a 1))) (Nat.beq (Nat.land a 1) 1) = _
  rw [lp_bit0, h]
  all_goals rfl

theorem lp_selK_f {x : ℕ} {L : List ℕ} {a : ℕ} (h : a.testBit 0 = false) :
    selK (x :: L) a = selK L (a >>> 1) := by
  change Bool.rec (motive := fun _ => ℕ) (selK L (Nat.shiftRight a 1))
    (Nat.xor x (selK L (Nat.shiftRight a 1))) (Nat.beq (Nat.land a 1) 1) = _
  rw [lp_bit0, h]
  all_goals rfl

theorem lp_selK_nil (a : ℕ) : selK [] a = 0 := rfl

theorem lp_selK_zero : ∀ L : List ℕ, selK L 0 = 0
  | [] => rfl
  | x :: L => by rw [lp_selK_f (Nat.zero_testBit 0), Nat.zero_shiftRight]; exact lp_selK_zero L

theorem lp_selK_xor : ∀ (L : List ℕ) (a b : ℕ), selK L (a ^^^ b) = selK L a ^^^ selK L b
  | [], _, _ => (Nat.zero_xor 0).symm
  | x :: L, a, b => by
    have ih := lp_selK_xor L (a >>> 1) (b >>> 1)
    cases ha : a.testBit 0 <;> cases hb : b.testBit 0
    · rw [lp_selK_f (by rw [Nat.testBit_xor, ha, hb]; all_goals rfl), lp_selK_f ha, lp_selK_f hb, lp_shr_xor, ih]
    · rw [lp_selK_t (by rw [Nat.testBit_xor, ha, hb]; all_goals rfl), lp_selK_f ha, lp_selK_t hb, lp_shr_xor,
        ih, lp_x3]
    · rw [lp_selK_t (by rw [Nat.testBit_xor, ha, hb]; all_goals rfl), lp_selK_t ha, lp_selK_f hb, lp_shr_xor,
        ih, lp_x2]
    · rw [lp_selK_f (by rw [Nat.testBit_xor, ha, hb]; all_goals rfl), lp_selK_t ha, lp_selK_t hb, lp_shr_xor,
        ih, ← lp_x1]

theorem lp_selK_lt : ∀ (L : List ℕ), (∀ x ∈ L, x < 2 ^ 24) → ∀ a, selK L a < 2 ^ 24
  | [], _, _ => Nat.two_pow_pos 24
  | x :: L, h, a => by
    have hL := lp_selK_lt L (fun y hy => h y (List.mem_cons_of_mem _ hy)) (a >>> 1)
    cases ha : a.testBit 0
    · rw [lp_selK_f ha]
      exact hL
    · rw [lp_selK_t ha]
      exact lp_xor_lt (h x List.mem_cons_self) hL

theorem lp_selK_mod : ∀ (E : List ℕ) (a : ℕ), selK E a = selK E (a % 2 ^ E.length)
  | [], _ => rfl
  | x :: E, a => by
    rw [List.length_cons]
    have h1 : (a % 2 ^ (E.length + 1)).testBit 0 = a.testBit 0 := by
      rw [Nat.testBit_mod_two_pow]
      simp
    have h2 : (a % 2 ^ (E.length + 1)) >>> 1 = (a >>> 1) % 2 ^ E.length := by
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      have : (1 + j < E.length + 1) ↔ (j < E.length) := by omega
      simp only [this]
    cases ha : a.testBit 0
    · rw [lp_selK_f ha, lp_selK_f (h1.trans ha), h2, ← lp_selK_mod E]
    · rw [lp_selK_t ha, lp_selK_t (h1.trans ha), h2, ← lp_selK_mod E]

theorem lp_rec_xor (r : ℕ → ℕ) (a b : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => if (a ^^^ b).testBit k then r k ^^^ acc else acc) n =
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if a.testBit k then r k ^^^ acc else acc) n ^^^
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if b.testBit k then r k ^^^ acc else acc) n
  | 0 => (Nat.zero_xor 0).symm
  | n + 1 => by
    simp only [lp_rec_succ]
    rw [lp_rec_xor r a b n, Nat.testBit_xor]
    generalize Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => if a.testBit k then r k ^^^ acc else acc) n = X
    generalize Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => if b.testBit k then r k ^^^ acc else acc) n = Y
    cases a.testBit n <;> cases b.testBit n <;>
      simp only [Bool.false_xor, Bool.true_xor, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        eq_self_iff_true, ↓reduceIte]
    · exact lp_x3 _ _ _
    · exact lp_x2 _ _ _
    · exact lp_x1 _ _ _

theorem lp_vmF_xor (M a b : ℕ) : vmF 24 M (a ^^^ b) = vmF 24 M a ^^^ vmF 24 M b := by
  rw [CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec]
  exact lp_rec_xor _ a b 24

theorem lp_rowF_xor (A B k : ℕ) : rowF 24 (A ^^^ B) k = rowF 24 A k ^^^ rowF 24 B k := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (((A ^^^ B) >>> (k * 24)) &&& maskN 24).testBit j =
    ((((A >>> (k * 24)) &&& maskN 24)) ^^^ ((B >>> (k * 24)) &&& maskN 24)).testBit j
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases A.testBit (k * 24 + j) <;> cases B.testBit (k * 24 + j) <;> cases (maskN 24).testBit j <;>
    rfl

theorem lp_rec_xorM (rA rB r : ℕ → ℕ) (hr : ∀ k, r k = rA k ^^^ rB k) (v : ℕ) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if v.testBit k then r k ^^^ acc else acc) n =
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if v.testBit k then rA k ^^^ acc else acc) n ^^^
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if v.testBit k then rB k ^^^ acc else acc) n
  | 0 => (Nat.zero_xor 0).symm
  | n + 1 => by
    simp only [lp_rec_succ]
    rw [lp_rec_xorM rA rB r hr v n, hr]
    cases v.testBit n <;> simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    exact lp_xor4 _ _ _ _

theorem lp_vmF_xorM (A B v : ℕ) : vmF 24 (A ^^^ B) v = vmF 24 A v ^^^ vmF 24 B v := by
  rw [CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec, CFSG.KC.F2W.vmF_rec]
  exact lp_rec_xorM _ _ _ (lp_rowF_xor A B) v 24

theorem lp_rec_zero (r : ℕ → ℕ) (v : ℕ) (hr : ∀ k, v.testBit k = true → r k = 0) : ∀ n,
    Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => if v.testBit k then r k ^^^ acc else acc) n = 0
  | 0 => rfl
  | n + 1 => by
    simp only [lp_rec_succ]
    rw [lp_rec_zero r v hr n]
    cases h : v.testBit n <;> simp only [Bool.false_eq_true, eq_self_iff_true, ↓reduceIte]
    rw [hr n h]
    all_goals rfl

theorem lp_vmF_zero (M : ℕ) : vmF 24 M 0 = 0 := by
  rw [CFSG.KC.F2W.vmF_rec]
  exact lp_rec_zero _ 0 (fun k h => by rw [Nat.zero_testBit] at h; exact absurd h Bool.false_ne_true) 24

theorem lp_vmF_zeroM (v : ℕ) : vmF 24 0 v = 0 := by
  rw [CFSG.KC.F2W.vmF_rec]
  refine lp_rec_zero _ v (fun k _ => ?_) 24
  change (0 >>> (k * 24)) &&& maskN 24 = 0
  rw [Nat.zero_shiftRight, Nat.zero_and]

theorem lp_vmF_lt (M v : ℕ) : vmF 24 M v < 2 ^ 24 := CFSG.KC.F2W.vmF_lt 24 M v

theorem lp_vmF_selK (v : ℕ) : ∀ (L : List ℕ) (m : ℕ),
    vmF 24 (selK L m) v = selK (L.map fun b => vmF 24 b v) m
  | [], _ => lp_vmF_zeroM v
  | x :: L, m => by
    rw [List.map_cons]
    cases hm : m.testBit 0
    · rw [lp_selK_f hm, lp_selK_f hm, lp_vmF_selK v L]
    · rw [lp_selK_t hm, lp_selK_t hm, lp_vmF_xorM, lp_vmF_selK v L]

theorem lp_selK_map_vmF (b : ℕ) : ∀ (E : List ℕ) (a : ℕ),
    selK (E.map (vmF 24 b)) a = vmF 24 b (selK E a)
  | [], _ => (lp_vmF_zero b).symm
  | x :: E, a => by
    rw [List.map_cons]
    cases ha : a.testBit 0
    · rw [lp_selK_f ha, lp_selK_f ha, lp_selK_map_vmF b E]
    · rw [lp_selK_t ha, lp_selK_t ha, lp_vmF_xor, lp_selK_map_vmF b E]

section Maps

variable {XB : ℕ → ℕ} {BT : List ℕ} {f : ℕ → ℕ}

theorem lp_f0 (hf : Equi XB BT f) : f 0 = 0 := by
  have h := hf.add 0 0 (Nat.two_pow_pos 24) (Nat.two_pow_pos 24)
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem lp_f_selK (hf : Equi XB BT f) : ∀ (L : List ℕ), (∀ x ∈ L, x < 2 ^ 24) → ∀ m,
    f (selK L m) = selK (L.map f) m
  | [], _, _ => lp_f0 hf
  | x :: L, h, m => by
    have hL : ∀ y ∈ L, y < 2 ^ 24 := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons]
    cases hm : m.testBit 0
    · rw [lp_selK_f hm, lp_selK_f hm, lp_f_selK hf L hL]
    · rw [lp_selK_t hm, lp_selK_t hm, hf.add _ _ (h x List.mem_cons_self) (lp_selK_lt L hL _),
        lp_f_selK hf L hL]

theorem lp_comm_mem (hf : Equi XB BT f) {b : ℕ} (hb : b ∈ BT) {x : ℕ} (hx : x < 2 ^ 24) :
    f (vmF 24 b x) = vmF 24 b (f x) := by
  obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hb
  have e : BT[s] = BT.getD s 0 := (List.getD_eq_getElem _ _ hs).symm
  rw [e]
  exact hf.comm s hs x hx

theorem lp_f_e (hf : Equi XB BT f) (m : ℕ) {v : ℕ} (hv : v < 2 ^ 24) :
    f (vmF 24 (selK BT m) v) = vmF 24 (selK BT m) (f v) := by
  rw [lp_vmF_selK, lp_vmF_selK, lp_f_selK hf _ (fun y hy => by
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
    exact lp_vmF_lt b v) m, List.map_map]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  exact lp_comm_mem hf hb hv

end Maps

theorem lp_e_span {E : List ℕ} {eT : ℕ}
    (hcrd : ∀ r < 24, selK E (crdK E (fget eT r 24)) = fget eT r 24) (y : ℕ) :
    ∃ a, vmF 24 eT y = selK E a := by
  rw [CFSG.KC.F2W.vmF_rec]
  suffices h : ∀ n ≤ 24, ∃ a, Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => if y.testBit k then rowF 24 eT k ^^^ acc else acc) n = selK E a from h 24 le_rfl
  intro n
  induction n with
  | zero => exact fun _ => ⟨0, (lp_selK_zero E).symm⟩
  | succ n ih =>
    intro hn
    obtain ⟨a, ha⟩ := ih (by omega)
    simp only [lp_rec_succ]
    split_ifs
    · refine ⟨crdK E (fget eT n 24) ^^^ a, ?_⟩
      rw [lp_selK_xor, hcrd n (by omega), ← ha]
      all_goals rfl
    · exact ⟨a, ha⟩

variable {XB : ℕ → ℕ} {BT U : List ℕ} {IMS : List (List (List ℕ))}

theorem lp_codesOK {nb i : ℕ} : ∀ cs : List ℕ, codesOK nb i cs = true →
    ∀ c ∈ cs, c / 32 ≤ i ∧ c % 32 < nb
  | [], _, _, hc => by cases hc
  | c :: cs, h, c', hc' => by
    obtain ⟨h1, h⟩ := lp_andB h
    obtain ⟨h2, h3⟩ := lp_andB h
    rcases List.mem_cons.1 hc' with rfl | hc'
    · exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2⟩
    · exact lp_codesOK cs h3 c' hc'

theorem lp_testsUK {i : ℕ} : ∀ T : List (List ℕ), testsUK XB BT U i T = true → ∀ t ∈ T,
    codesOK (lenL BT) i t.tail = true ∧
      Nat.beq (bitN (memK XB (sumU BT U t.tail))) (t.headD 2) = true
  | [], _, _, ht => by cases ht
  | t :: T, h, t', ht' => by
    obtain ⟨h1, h⟩ := lp_andB h
    obtain ⟨h2, h3⟩ := lp_andB h
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact ⟨h1, h2⟩
    · exact lp_testsUK T h3 t' ht'

theorem lp_eqL : ∀ a b : List ℕ, eqLL.eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: a, y :: b, h => by
    obtain ⟨h1, h2⟩ := lp_andB h
    rw [Nat.eq_of_beq_eq_true h1, lp_eqL a b h2]

theorem lp_eqLL : ∀ A B : List (List ℕ), eqLL A B = true → A = B
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: A, y :: B, h => by
    obtain ⟨h1, h2⟩ := lp_andB h
    rw [lp_eqL x y h1, lp_eqLL A B h2]

theorem lp_imgs_inner (b : ℕ) : ∀ E : List ℕ,
    List.rec (motive := fun _ => List ℕ) List.nil
      (fun e _ ih2 => strictL (vmF (nat_lit 24) b e) fun v => List.cons v ih2) E =
      E.map (vmF 24 b)
  | [] => rfl
  | e :: E => by
    rw [List.map_cons, ← lp_imgs_inner b E]
    exact lp_strictL _ _

theorem lp_imgsK (E : List ℕ) : ∀ BT : List ℕ, imgsK BT E = BT.map fun b => E.map (vmF 24 b)
  | [] => rfl
  | b :: BT => by
    rw [List.map_cons, ← lp_imgsK E BT, ← lp_imgs_inner b E]
    all_goals rfl

theorem lp_levelOK {i : ℕ} {E : List ℕ} {m u : ℕ} {T : List (List ℕ)} {IM : List (List ℕ)}
    (h : levelOK XB BT U i E m u T IM = true) :
    (∀ r < 24, selK E (crdK E (fget (selK BT m) r 24)) = fget (selK BT m) r 24) ∧
      vmF 24 (selK BT m) u = u ∧ memK XB u = true ∧ testsUK XB BT U i T = true ∧
      IM = imgsK BT E := by
  unfold levelOK at h
  rw [lp_strictB] at h
  obtain ⟨-, h⟩ := lp_andB h
  obtain ⟨h1, h⟩ := lp_andB h
  obtain ⟨h2, h⟩ := lp_andB h
  obtain ⟨h3, h⟩ := lp_andB h
  obtain ⟨h4, h5⟩ := lp_andB h
  refine ⟨fun r hr => ?_, Nat.eq_of_beq_eq_true h2, h3, h4, lp_eqLL _ _ h5⟩
  have := lp_allN h1 r hr
  rw [lp_strictB] at this
  exact Nat.eq_of_beq_eq_true this

theorem lp_slotU_lt (c : ℕ) : slotU BT U c < 2 ^ 24 := lp_vmF_lt _ _

theorem lp_sumU_lt : ∀ cs : List ℕ, sumU BT U cs < 2 ^ 24
  | [] => Nat.two_pow_pos 24
  | c :: cs => lp_xor_lt (lp_slotU_lt c) (lp_sumU_lt cs)

theorem lp_pack_low : ∀ (SL : List ℕ) (r0 p : ℕ), p < 24 * r0 →
    (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun c _ ih r => Nat.lor (Nat.shiftLeft (slotU BT U c) (Nat.mul 24 r)) (ih (Nat.succ r)))
      SL r0).testBit p = false
  | [], _, p, _ => Nat.zero_testBit p
  | c :: SL, r0, p, hp => by
    change (((slotU BT U c) <<< (24 * r0)) ||| _).testBit p = false
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, lp_pack_low SL (r0 + 1) p (by omega)]
    have : ¬ (p ≥ 24 * r0) := by omega
    simp [this]

theorem lp_pack_bit : ∀ (SL : List ℕ) (r0 k j : ℕ), k < SL.length → j < 24 →
    (List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
      (fun c _ ih r => Nat.lor (Nat.shiftLeft (slotU BT U c) (Nat.mul 24 r)) (ih (Nat.succ r)))
      SL r0).testBit (24 * (r0 + k) + j) = (slotU BT U (SL.getD k 0)).testBit j
  | [], _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | c :: SL, r0, 0, j, _, hj => by
    change (((slotU BT U c) <<< (24 * r0)) ||| _).testBit _ = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, lp_pack_low SL (r0 + 1) _ (by omega),
      List.getD_cons_zero]
    have e : 24 * (r0 + 0) + j - 24 * r0 = j := by omega
    have : 24 * (r0 + 0) + j ≥ 24 * r0 := by omega
    simp [e, this]
  | c :: SL, r0, k + 1, j, hk, hj => by
    change (((slotU BT U c) <<< (24 * r0)) ||| _).testBit _ = _
    have e : 24 * (r0 + (k + 1)) + j = 24 * (r0 + 1 + k) + j := by omega
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, e, lp_pack_bit SL (r0 + 1) k j
      (by simpa using hk) hj, List.getD_cons_succ]
    have hb : (slotU BT U c).testBit (24 * (r0 + 1 + k) + j - 24 * r0) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lp_slotU_lt c)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb, Bool.and_false, Bool.false_or]

theorem lp_rowF_packU {SL : List ℕ} {r : ℕ} (hr : r < SL.length) :
    rowF 24 (packU BT U SL) r = slotU BT U (SL.getD r 0) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change ((packU BT U SL >>> (r * 24)) &&& maskN 24).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have hm : maskN 24 = 2 ^ 24 - 1 := by
    change Nat.sub (pw2 24) 1 = _
    rw [lp_pw2]
    all_goals rfl
  rw [hm, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 24
  · have e : r * 24 + j = 24 * (0 + r) + j := by ring
    rw [e]
    simp only [hj, decide_true, Bool.and_true]
    exact lp_pack_bit SL 0 r j hr hj
  · have hb : (slotU BT U (SL.getD r 0)).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (lp_slotU_lt _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb]
    simp [hj]

theorem lp_agree {f g : ℕ → ℕ} (hf : Equi XB BT f) (hg : Equi XB BT g) {P : ℕ}
    (h : ∀ r < 24, f (rowF 24 P r) = g (rowF 24 P r)) (w : ℕ) :
    f (vmF 24 P w) = g (vmF 24 P w) := by
  rw [CFSG.KC.F2W.vmF_rec]
  suffices H : ∀ n ≤ 24, Nat.rec (motive := fun _ => ℕ) 0
      (fun k acc => if w.testBit k then rowF 24 P k ^^^ acc else acc) n < 2 ^ 24 ∧
      f (Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => if w.testBit k then rowF 24 P k ^^^ acc else acc) n) =
      g (Nat.rec (motive := fun _ => ℕ) 0
        (fun k acc => if w.testBit k then rowF 24 P k ^^^ acc else acc) n) from (H 24 le_rfl).2
  intro n
  induction n with
  | zero => exact fun _ => ⟨Nat.two_pow_pos 24, by
    change f 0 = g 0
    rw [lp_f0 hf, lp_f0 hg]⟩
  | succ n ih =>
    intro hn
    obtain ⟨hlt, heq⟩ := ih (by omega)
    simp only [lp_rec_succ]
    have hrow : rowF 24 P n < 2 ^ 24 := CFSG.KC.F2W.rowF_lt 24 P n
    split_ifs
    · refine ⟨lp_xor_lt hrow hlt, ?_⟩
      rw [hf.add _ _ hrow hlt, hg.add _ _ hrow hlt, heq, h n (by omega)]
    · exact ⟨hlt, heq⟩

end Lemmas

end CFSG.KC.Co1LeafP

end
