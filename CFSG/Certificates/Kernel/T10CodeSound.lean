module

public import Certificates.Data.Kernel.T10Code
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModT10Data
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.T10Code

open CFSG.OddStandard.AltStdSmall4.ModT10 CFSG.OddStandard.AltStdSmall4.ModT10.T10

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_inj {a b : Bool} : b2z a = b2z b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem zmod2_neg (z : ZMod 2) : -z = z := by
  revert z
  decide

theorem xor_nd (a b : Bool) : (a ^^ b) = !decide (a = b) := by
  cases a <;> cases b <;> rfl

theorem b2z_beq_zero (a : Bool) : (b2z a == 0) = !a := by
  cases a <;> rfl

def atW (w : W10) (j : Nat) : T10 :=
  ⟨b2z (w.w0.testBit j), b2z (w.w1.testBit j), b2z (w.w2.testBit j), b2z (w.w3.testBit j),
    b2z (w.w4.testBit j), b2z (w.w5.testBit j), b2z (w.ws.testBit j), b2z (w.wa.testBit j),
    b2z (w.wb.testBit j), b2z (w.wc.testBit j)⟩

theorem atW_mulW (p q : W10) (j : Nat) : atW (mulW p q) j = atW p j * atW q j := by
  ext <;> simp only [atW, mulW, Nat.xor_eq, Nat.land_eq, Nat.testBit_xor, Nat.testBit_and,
    b2z_xor, b2z_and, mul_x0, mul_x1, mul_x2, mul_x3, mul_x4, mul_x5, mul_s, mul_a, mul_b,
    mul_c] <;> ring

theorem atW_invW (p : W10) (j : Nat) : atW (invW p) j = (atW p j)⁻¹ := by
  ext <;> simp only [atW, invW, Nat.xor_eq, Nat.land_eq, Nat.testBit_xor, Nat.testBit_and,
    b2z_xor, b2z_and, inv_x0, inv_x1, inv_x2, inv_x3, inv_x4, inv_x5, inv_s, inv_a, inv_b,
    inv_c, sub_eq_add_neg, neg_add, zmod2_neg, neg_mul] <;> ring

theorem atW_ZW (j : Nat) : atW ZW j = 1 := by
  ext <;> simp [atW, ZW, b2z] <;> rfl

theorem difW_testBit (p q : W10) (j : Nat) :
    (difW p q).testBit j = !decide (atW p j = atW q j) := by
  simp only [difW, atW, Nat.lor_eq, Nat.xor_eq, Nat.testBit_or, Nat.testBit_xor, T10.mk.injEq,
    b2z_inj, xor_nd, Bool.decide_and, Bool.not_and, Bool.or_assoc]

theorem tb_eq (n i : Nat) : tb n i = n.testBit i := by
  rw [tb, Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;>
    simp [Nat.land_eq, Nat.and_one_is_mod, h] <;> rfl

theorem bitv (x k : Nat) : Nat.land (Nat.shiftRight x k) 1 = if x.testBit k then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, Nat.land_eq,
    Nat.shiftRight_eq', Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (x >>> k) with h | h <;> simp [h]

theorem testBit_ite_shift (c : Bool) (n j : Nat) :
    (Nat.shiftLeft (if c then 1 else 0) n).testBit j = (c && decide (n = j)) := by
  rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  cases c <;> simp [Nat.testBit_two_pow]

def planeN (k n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun g acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight g k) 1) g)) n

theorem testBit_planeN (k n j : Nat) : (planeN k n).testBit j = (decide (j < n) && j.testBit k) := by
  induction n with
  | zero => simp [planeN]
  | succ n ih =>
    change (Nat.lor (planeN k n) (Nat.shiftLeft (Nat.land (Nat.shiftRight n k) 1) n)).testBit j = _
    rw [Nat.lor_eq, Nat.testBit_or, ih, bitv, testBit_ite_shift]
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · simp [h, Nat.lt_succ_of_lt h, show n ≠ j by omega]
    · simp
    · simp [show ¬ j < n by omega, show ¬ j < n + 1 by omega, show n ≠ j by omega]

theorem testBit_plane (k j : Nat) : (plane k).testBit j = (decide (j < 1024) && j.testBit k) :=
  testBit_planeN k 1024 j

theorem testBit_ALL (j : Nat) : ALL.testBit j = decide (j < 1024) := by
  simp only [ALL, Nat.sub_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow_sub_one]

theorem testBit_bc (x k j : Nat) : (bc x k).testBit j = (decide (j < 1024) && x.testBit k) := by
  rw [bc, bitv, Nat.mul_eq]
  cases x.testBit k <;> simp [testBit_ALL]

theorem b2z_testBit (j k : Nat) : b2z (j.testBit k) = ((j / 2 ^ k % 2 : ℕ) : ZMod 2) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (j / 2 ^ k) with h | h <;> simp [h, b2z]

theorem ofCode_eq (j : Nat) : ofCode j = ⟨b2z (j.testBit 0), b2z (j.testBit 1),
    b2z (j.testBit 2), b2z (j.testBit 3), b2z (j.testBit 4), b2z (j.testBit 5), b2z (j.testBit 6),
    b2z (j.testBit 7), b2z (j.testBit 8), b2z (j.testBit 9)⟩ := by
  simp only [b2z_testBit, Nat.pow_zero, Nat.div_one]
  rfl

theorem atW_PL {j : Nat} (hj : j < 1024) : atW PL j = ofCode j := by
  rw [ofCode_eq]
  simp only [atW, PL, testBit_plane, hj, decide_true, Bool.true_and]

theorem atW_BC (x : Nat) {j : Nat} (hj : j < 1024) : atW (BC x) j = ofCode x := by
  rw [ofCode_eq]
  simp only [atW, BC, testBit_bc, hj, decide_true, Bool.true_and]

theorem tm_eq : tm = ofCode 64 := by
  ext <;> rfl

theorem inQ_atW (w : W10) (j : Nat) :
    inQ (atW w j) = !(w.ws.testBit j || w.wa.testBit j || (w.wb.testBit j || w.wc.testBit j)) := by
  simp only [inQ, atW, b2z_beq_zero, Bool.not_or, Bool.and_assoc]

section Pred

variable {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j)
include hP

theorem inQc_eq {x : Nat} (hx : x < 1024) : inQc P x = inQ (ofCode x) := by
  rw [← hP x hx, inQ_atW, inQc, tb_eq, QMW, Nat.lor_eq, Nat.lor_eq, Nat.lor_eq, Nat.testBit_or,
    Nat.testBit_or, Nat.testBit_or]

theorem inMc_eq {x : Nat} (hx : x < 1024) : inMc P x = inM (ofCode x) := by
  rw [← hP x hx, inMc, tb_eq]
  simp only [inM, atW, b2z_beq_zero]

theorem sq1c_eq {x : Nat} (hx : x < 1024) : sq1c P x = (ofCode x * ofCode x == 1) := by
  rw [sq1c, tb_eq, SQW, difW_testBit, atW_mulW, atW_ZW, hP x hx, Bool.not_not]
  rfl

theorem isInvc_eq {x : Nat} (hx : x < 1024) : isInvc P x = isInv (ofCode x) := by
  rw [isInvc, tb_eq, tb_eq, SQW, NZW, difW_testBit, difW_testBit, atW_mulW, atW_ZW, hP x hx,
    Bool.not_not, isInv]
  rfl

theorem commc_eq {g x : Nat} (hg : g < 1024) (hx : x < 1024) :
    commc P g x = commB (ofCode g) (ofCode x) := by
  rw [commc, tb_eq, CDW, difW_testBit, atW_mulW, atW_mulW, hP g hg, atW_BC x hg, Bool.not_not,
    commB]
  rfl

theorem tb_CJW {g x : Nat} (hg : g < 1024) (hx : x < 1024) :
    (!tb (CJW P x) g) = commB (ofCode g * ofCode x * (ofCode g)⁻¹) tm := by
  rw [tb_eq, CJW, difW_testBit]
  simp only [atW_mulW, atW_invW, hP g hg, atW_BC _ hg, Bool.not_not, commB, tm_eq]
  rfl

end Pred

theorem allR_spec {p : Nat → Bool} {lo N : Nat} (h : allR p lo N = true) :
    ∀ i < N, p (lo + i) = true := by
  induction N with
  | zero => intro i hi; omega
  | succ N ih =>
    change Bool.rec (motive := fun _ => Bool) false (allR p lo N) (p (Nat.add lo N)) = true at h
    intro i hi
    cases hp : p (Nat.add lo N)
    · rw [hp] at h
      exact absurd h Bool.false_ne_true
    · rw [hp] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih h i hi
      · exact hp

theorem anyN_spec {p : Nat → Bool} {N : Nat} (h : anyN p N = true) : ∃ i < N, p i = true := by
  induction N with
  | zero => exact absurd h Bool.false_ne_true
  | succ N ih =>
    change Bool.rec (motive := fun _ => Bool) (anyN p N) true (p N) = true at h
    cases hp : p N
    · rw [hp] at h
      obtain ⟨i, hi, hpi⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hpi⟩
    · exact ⟨N, Nat.lt_succ_self N, hp⟩

theorem cntN_eq (p : Nat → Bool) (N : Nat) : cntN p N = ((List.range N).filter p).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change Bool.rec (motive := fun _ => Nat) (cntN p N) (Nat.succ (cntN p N)) (p N) = _
    rw [List.range_succ, List.filter_append, List.length_append, ← ih]
    cases hp : p N <;> simp [hp]

theorem cntN_congr {p q : Nat → Bool} {N : Nat} (h : ∀ i < N, p i = q i) : cntN p N = cntN q N := by
  rw [cntN_eq, cntN_eq, List.filter_congr fun i hi => h i (List.mem_range.1 hi)]

theorem length_filter_allL (p : T10 → Bool) :
    ((allL ()).filter p).length = cntN (fun g => p (ofCode g)) 1024 := by
  rw [cntN_eq, allL, List.filter_map, List.length_map]
  rfl

theorem allR_all {p : Nat → Bool} (h : ∀ k < 8, allR p (128 * k) 128 = true) :
    ∀ x < 1024, p x = true := by
  intro x hx
  have := allR_spec (h (x / 128) (by omega)) (x % 128) (Nat.mod_lt _ (by omega))
  rwa [Nat.div_add_mod] at this

theorem all_of_chunks {p : Nat → Bool} (h0 : allR p 0 128 = true) (h1 : allR p 128 128 = true)
    (h2 : allR p 256 128 = true) (h3 : allR p 384 128 = true) (h4 : allR p 512 128 = true)
    (h5 : allR p 640 128 = true) (h6 : allR p 768 128 = true) (h7 : allR p 896 128 = true) :
    ∀ x < 1024, p x = true :=
  allR_all fun k hk => match k, hk with
    | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
    | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7

theorem or_or_imp {a d e e' : Bool} (h : e' = true → e = true) (hb : (a || (d || e')) = true) :
    (a || (d || e)) = true := by
  cases a <;> cases d <;> simp_all

theorem t10CheckB_of {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j)
    (h : ∀ x < 1024, FB P x = true) : t10CheckB () = true := by
  rw [t10CheckB, List.all_eq_true]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hx := List.mem_range.1 hx
  have hb := h x hx
  rw [FB, inQc_eq hP hx, sq1c_eq hP hx, inMc_eq hP hx,
    cntN_congr (p := fun g => inQc P g && commc P g x)
      (q := fun g => inQ (ofCode g) && commB (ofCode g) (ofCode x))
      (fun g hg => by rw [inQc_eq hP hg, commc_eq hP hg hx])] at hb
  rw [length_filter_allL]
  exact hb

theorem t10CheckC_of {P : W10} (hP : ∀ j < 1024, atW P j = ofCode j) (hc : cTc P = 128)
    (hi : iTc P = 55) (h : ∀ x < 1024, FC P x = true) : t10CheckC () = true := by
  have hcT : ((allL ()).filter fun g => commB g tm).length = 128 := by
    rw [length_filter_allL, ← hc, cTc, tm_eq]
    exact cntN_congr fun g hg => (commc_eq hP hg (by omega)).symm
  have hiT : ((allL ()).filter fun g => commB g tm && isInv g).length = 55 := by
    rw [length_filter_allL, ← hi, iTc, tm_eq]
    exact cntN_congr fun g hg => by rw [commc_eq hP hg (by omega), isInvc_eq hP hg]
  rw [t10CheckC]
  simp only [hcT, hiT, beq_self_eq_true, Bool.true_and, List.all_eq_true]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  have hx := List.mem_range.1 hx
  have hb := h x hx
  rw [FC, inMc_eq hP hx, inQc_eq hP hx, isInvc_eq hP hx,
    cntN_congr (p := fun g => commc P g x) (q := fun g => commB (ofCode g) (ofCode x))
      (fun g hg => commc_eq hP hg hx),
    cntN_congr (p := fun g => commc P g x && isInvc P g)
      (q := fun g => commB (ofCode g) (ofCode x) && isInv (ofCode g))
      (fun g hg => by rw [commc_eq hP hg hx, isInvc_eq hP hg])] at hb
  rw [length_filter_allL, length_filter_allL]
  refine or_or_imp (fun ha => ?_) hb
  obtain ⟨g, hg, hpg⟩ := anyN_spec ha
  rw [tb_CJW hP hg hx] at hpg
  exact List.any_eq_true.2 ⟨ofCode g, List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩, hpg⟩

end CFSG.KC.T10Code
