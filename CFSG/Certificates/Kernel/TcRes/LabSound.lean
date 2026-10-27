module

public import Certificates.Data.TcRes
public import Certificates.Data.Kernel.TcRes.C2Moved
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.TcRes

open Certificates.TcRes CFSG.TcRes.TK

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem brecN_eq (f t : ℕ) (b : Bool) : Bool.rec (motive := fun _ => ℕ) f t b = cond b t f := by
  cases b <;> rfl

theorem brecB_eq (f t : Bool) (b : Bool) :
    Bool.rec (motive := fun _ => Bool) f t b = cond b t f := by
  cases b <;> rfl

theorem nbeq_eq (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_eq]

theorem nble_eq (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

theorem nblt_eq (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  change Nat.ble (a + 1) b = _
  rw [nble_eq]
  rfl

theorem nadd_eq (a b : ℕ) : Nat.add a b = a + b := rfl

theorem nmul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem nsub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl

theorem nmod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

theorem npow_eq (a b : ℕ) : Nat.pow a b = a ^ b := rfl

theorem ndiv_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem any_congr' {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem allLt_iff (c : ℕ) (p : ℕ → Bool) : allLt c p = true ↔ ∀ m < c, p m = true := by
  induction c with
  | zero => simp [allLt]
  | succ c ih =>
    change andB (p c) (allLt c p) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ m hm
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h | rfl
      · exact h2 m h
      · exact h1
    · intro h
      exact ⟨h c (Nat.lt_succ_self c), fun m hm => h m (Nat.lt_succ_of_lt hm)⟩

theorem anyLt_iff (c : ℕ) (p : ℕ → Bool) : anyLt c p = true ↔ ∃ m < c, p m = true := by
  induction c with
  | zero => simp [anyLt]
  | succ c ih =>
    change orB (p c) (anyLt c p) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨m, hm, h⟩)
      · exact ⟨c, Nat.lt_succ_self c, h⟩
      · exact ⟨m, Nat.lt_succ_of_lt hm, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h' | rfl
      · exact Or.inr ⟨m, h', h⟩
      · exact Or.inl h

theorem land15 (x : ℕ) : Nat.land x 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4

theorem land255 (x : ℕ) : Nat.land x 255 = x % 256 := Nat.and_two_pow_sub_one_eq_mod x 8

theorem shr_eq (x k : ℕ) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

@[expose] def tkTg : TcrTg → ℕ
  | .A => 0 | .twA => 1 | .D => 2 | .twD => 3 | .E6 => 4 | .E7 => 5 | .E8 => 6 | .twE6 => 7
  | .triD4 => 8

@[expose] noncomputable def tkLab (l : TcrLab) : ℕ := lab (tkTg l.t) l.r l.n

@[expose] def tkKind : ℕ → TcrKind
  | 0 => .inner | 1 => .suN | 2 => .twoD | _ => .exc

@[expose] noncomputable def tkCd (d : ℕ) : TcrCData := ⟨dE d, dR d, dN d, [tkKind (dK d)]⟩

@[expose] noncomputable def tkKs (m : ℕ) : List TcrKind :=
  ((List.range 4).filter fun k => bit m k).map tkKind

@[expose] noncomputable def tkCd5 (d : ℕ) : TcrCData := ⟨dE d, dR d, dN d, tkKs (dKs d)⟩

theorem tkTg_lt (t : TcrTg) : tkTg t < 9 := by cases t <;> decide

theorem tkTg_inj {t t' : TcrTg} (h : tkTg t = tkTg t') : t = t' := by
  cases t <;> cases t' <;> first | rfl | (simp [tkTg] at h)

theorem lab_dec {t r n : ℕ} (ht : t < 16) (hr : r < 16) :
    Nat.land (lab t r n) 15 = t ∧ Nat.land (Nat.shiftRight (lab t r n) 4) 15 = r ∧
      Nat.shiftRight (lab t r n) 8 = n := by
  simp only [lab, land15, shr_eq, nadd_eq, nmul_eq]
  refine ⟨by omega, by omega, by omega⟩

theorem tkLab_dec {l : TcrLab} (hl : l.r < 16) :
    Nat.land (tkLab l) 15 = tkTg l.t ∧ Nat.land (Nat.shiftRight (tkLab l) 4) 15 = l.r ∧
      Nat.shiftRight (tkLab l) 8 = l.n :=
  lab_dec (by have := tkTg_lt l.t; omega) hl

theorem tkLab_inj {l l' : TcrLab} (hl : l.r < 16) (hl' : l'.r < 16) (h : tkLab l = tkLab l') :
    l = l' := by
  obtain ⟨a1, a2, a3⟩ := tkLab_dec hl
  obtain ⟨b1, b2, b3⟩ := tkLab_dec hl'
  rw [h] at a1 a2 a3
  obtain ⟨t, r, n⟩ := l
  obtain ⟨t', r', n'⟩ := l'
  simp only at a1 a2 a3 b1 b2 b3
  have : t = t' := tkTg_inj (a1.symm.trans b1)
  subst this
  simp only [TcrLab.mk.injEq, true_and]
  exact ⟨a2.symm.trans b2, a3.symm.trans b3⟩

theorem tkLab_lt {l : TcrLab} (hl : l.r < 16) (hn : l.n < 2 ^ 31) : tkLab l < NOLAB := by
  have := tkTg_lt l.t
  simp only [tkLab, lab, NOLAB, nadd_eq, nmul_eq]
  omega

theorem compLab_eq (r N k n : ℕ) :
    compLab r N k n = tkLab (tcrComponentLabel r N (tkKind k) n) := by
  rcases k with _ | _ | _ | k
  · simp only [compLab, brecN_eq, nbeq_eq, tkKind, tcrComponentLabel, Nat.succ_eq_add_one,
      nmul_eq, nsub_eq]
    by_cases h1 : N = r * (r + 1)
    · rw [if_pos h1, decide_eq_true h1]
      rfl
    rw [if_neg h1, decide_eq_false h1]
    by_cases h2 : N = 2 * r * (r - 1)
    · rw [if_pos h2, decide_eq_true h2]
      rfl
    rw [if_neg h2, decide_eq_false h2]
    by_cases h3 : r = 6
    · rw [if_pos h3, decide_eq_true h3]
      rfl
    rw [if_neg h3, decide_eq_false h3]
    by_cases h4 : r = 7
    · rw [if_pos h4, decide_eq_true h4]
      rfl
    rw [if_neg h4, decide_eq_false h4]
    rfl
  · simp [compLab, brecN_eq, nbeq_eq, tkKind, tcrComponentLabel, tkLab, tkTg]
  · simp [compLab, brecN_eq, nbeq_eq, tkKind, tcrComponentLabel, tkLab, tkTg]
  · simp only [compLab, brecN_eq, nbeq_eq, tkKind, tcrComponentLabel]
    by_cases h3 : r = 6
    · rw [if_pos h3, decide_eq_true h3]
      rfl
    rw [if_neg h3, decide_eq_false h3]
    rfl

@[expose] noncomputable def tkEx (l : TcrLab) : ℕ := (((tcrLabelClass l).tail.head?).map tkLab).getD NOLAB

theorem extraLab_eq {l : TcrLab} (hl : l.r < 16) : extraLab (tkLab l) = tkEx l := by
  obtain ⟨a1, a2, a3⟩ := tkLab_dec hl
  obtain ⟨t, r, n⟩ := l
  simp only at a1 a2 a3 hl
  simp only [extraLab, strictN_eq, a1, a2, a3, brecN_eq, nbeq_eq, andB_eq]
  cases t <;> simp only [tkTg, tkEx, tcrLabelClass] <;> (try split_ifs) <;>
    simp_all [tkLab, tkTg, nmul_eq, ndiv_eq, nmod_eq]

theorem mem_class {l m : TcrLab} (hm : m ∈ tcrLabelClass l) :
    (m = l ∨ m.r ≤ 3) ∧ m.n ≤ 2 * l.n := by
  obtain ⟨t, r, n⟩ := l
  simp only [tcrLabelClass] at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact ⟨Or.inl rfl, by simp; omega⟩
  · cases t <;> simp only at hm <;> (try split_ifs at hm) <;> simp_all <;> omega

theorem class_eq (l : TcrLab) :
    tcrLabelClass l = l :: ((tcrLabelClass l).tail.head?).toList := by
  obtain ⟨t, r, n⟩ := l
  cases t <;> simp only [tcrLabelClass] <;> (try split_ifs) <;> rfl

theorem anyLab_eq (p : ℕ → Bool) {l : TcrLab} (hl : l.r < 16) (hn : l.n < 2 ^ 30) :
    anyLab p (tkLab l) = (tcrLabelClass l).any fun m => p (tkLab m) := by
  rw [anyLab, strictB_eq, extraLab_eq hl, orB_eq, andB_eq, notB_eq, nbeq_eq]
  conv_rhs => rw [class_eq l]
  cases hx : (tcrLabelClass l).tail.head? with
  | none => simp [tkEx, hx]
  | some m =>
    have hm : m ∈ tcrLabelClass l := by
      rw [class_eq l, hx]
      simp
    obtain ⟨h1, h2⟩ := mem_class hm
    have hmr : m.r < 16 := by rcases h1 with rfl | h <;> omega
    have hne : tkLab m ≠ NOLAB := (tkLab_lt hmr (by omega)).ne
    simp [tkEx, hx, hne]

theorem class_r {l m : TcrLab} (hl : l.r < 16) (hm : m ∈ tcrLabelClass l) : m.r < 16 := by
  rcases (mem_class hm).1 with rfl | h <;> omega

theorem split3_eq {l : TcrLab} (hl : l.r < 16) : split3 (tkLab l) = tcrSplitT 3 l := by
  obtain ⟨a1, -, a3⟩ := tkLab_dec hl
  rw [split3, strictB_eq, strictB_eq, a1, a3]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tcrSplitT, tcrUntw, untw, m3, p3, tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq,
    nble_eq, nmod_eq, npow_eq, nsub_eq, nadd_eq] <;> tauto

theorem half3_eq {l : TcrLab} (hl : l.r < 16) : half3 (tkLab l) = tcrHalfSplitT 3 l := by
  obtain ⟨a1, a2, a3⟩ := tkLab_dec hl
  rw [half3, strictB_eq, strictB_eq, strictB_eq, a1, a2, a3, tcrHalfSplitT, ← split3_eq hl]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq, m3, p3, nmod_eq, npow_eq, nsub_eq,
    nadd_eq] <;> tauto

theorem splitP_eq (p : ℕ) {l : TcrLab} (hl : l.r < 16) : splitP p (tkLab l) = tcrSplitT p l := by
  obtain ⟨a1, -, a3⟩ := tkLab_dec hl
  rw [splitP, strictB_eq, strictB_eq, a1, a3]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tcrSplitT, tcrUntw, untw, mP, pP, tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq,
    nble_eq, nmod_eq, npow_eq, nsub_eq, nadd_eq] <;> tauto

theorem halfP_eq (p : ℕ) {l : TcrLab} (hl : l.r < 16) :
    halfP p (tkLab l) = tcrHalfSplitT p l := by
  obtain ⟨a1, a2, a3⟩ := tkLab_dec hl
  rw [halfP, strictB_eq, strictB_eq, strictB_eq, a1, a2, a3, tcrHalfSplitT, ← splitP_eq p hl]
  obtain ⟨t, r, n⟩ := l
  rw [Bool.eq_iff_iff]
  cases t <;> simp [tkTg, orB_eq, andB_eq, notB_eq, nbeq_eq, mP, pP, nmod_eq, npow_eq, nsub_eq,
    nadd_eq] <;> tauto

theorem meets_eq {a b : TcrLab} (ha : a.r < 16) (han : a.n < 2 ^ 30) (hb : b.r < 16)
    (hbn : b.n < 2 ^ 30) :
    meets (tkLab a) (tkLab b) =
      (tcrLabelClass a).any fun l => (tcrLabelClass b).contains l := by
  rw [meets, strictB_eq, extraLab_eq hb, anyLab_eq _ ha han]
  apply any_congr'
  intro m hm
  have hmr := class_r ha hm
  have hmn : m.n < 2 ^ 31 := by have := (mem_class hm).2; omega
  rw [class_eq b]
  cases hx : (tcrLabelClass b).tail.head? with
  | none =>
    have hne : tkLab m ≠ NOLAB := (tkLab_lt hmr hmn).ne
    simp only [tkEx, hx, Option.map_none, Option.getD_none, Option.toList_none, orB_eq, nbeq_eq]
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, hne, decide_false,
      Bool.or_false]
    by_cases h : m = b
    · subst h; simp
    · have : tkLab m ≠ tkLab b := fun h' => h (tkLab_inj hmr hb h')
      simp [h, this]
  | some c =>
    have hc : c ∈ tcrLabelClass b := by
      rw [class_eq b, hx]
      simp
    have hcr := class_r hb hc
    simp only [tkEx, hx, Option.map_some, Option.getD_some, Option.toList_some, orB_eq, nbeq_eq]
    have e1 : (tkLab m = tkLab b) ↔ m = b :=
      ⟨tkLab_inj hmr hb, fun h => h ▸ rfl⟩
    have e2 : (tkLab m = tkLab c) ↔ m = c :=
      ⟨tkLab_inj hmr hcr, fun h => h ▸ rfl⟩
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq]
    by_cases h1 : m = b <;> by_cases h2 : m = c <;> simp_all

theorem dR_lt (d : ℕ) : dR d < 16 := by
  rw [dR, land15]; exact Nat.mod_lt _ (by norm_num)

theorem dE_lt (d : ℕ) : dE d < 16 := by
  rw [dE, land15]; exact Nat.mod_lt _ (by norm_num)

theorem compLab_valid (r N : ℕ) (k : TcrKind) (n : ℕ) (hr : r < 16) :
    (tcrComponentLabel r N k n).r < 16 ∧ (tcrComponentLabel r N k n).n = n := by
  cases k <;> simp only [tcrComponentLabel] <;> (try split_ifs) <;> simp [hr]

theorem labOf_eq (d f : ℕ) :
    labOf d f = tkLab (tcrComponentLabel (tkCd d).r (tkCd d).N (tkKind (dK d)) ((tkCd d).e * f)) :=
  compLab_eq _ _ _ _

theorem tcrLabsOf_tkCd (d f : ℕ) :
    tcrLabsOf (tkCd d) f =
      tcrLabelClass (tcrComponentLabel (tkCd d).r (tkCd d).N (tkKind (dK d)) ((tkCd d).e * f)) := by
  simp [tcrLabsOf, tkCd]

theorem labOf_valid (d f : ℕ) (hf : f ≤ 3) :
    (tcrComponentLabel (tkCd d).r (tkCd d).N (tkKind (dK d)) ((tkCd d).e * f)).r < 16 ∧
    (tcrComponentLabel (tkCd d).r (tkCd d).N (tkKind (dK d)) ((tkCd d).e * f)).n < 2 ^ 30 := by
  obtain ⟨h1, h2⟩ := compLab_valid (tkCd d).r (tkCd d).N (tkKind (dK d)) ((tkCd d).e * f)
    (dR_lt d)
  refine ⟨h1, ?_⟩
  rw [h2]
  have := dE_lt d
  change dE d * f < _
  nlinarith

theorem anyLab_labOf (q : ℕ → Bool) (q' : TcrLab → Bool)
    (hq : ∀ l : TcrLab, l.r < 16 → q (tkLab l) = q' l) (d f : ℕ) (hf : f ≤ 3) :
    anyLab q (labOf d f) = (tcrLabsOf (tkCd d) f).any q' := by
  obtain ⟨h1, h2⟩ := labOf_valid d f hf
  rw [labOf_eq, anyLab_eq q h1 h2, tcrLabsOf_tkCd]
  exact any_congr' fun m hm => hq m (class_r h1 hm)

theorem meets_labOf (a b f : ℕ) (hf : f ≤ 3) :
    meets (labOf a f) (labOf b f) =
      (tcrLabsOf (tkCd a) f).any fun l => (tcrLabsOf (tkCd b) f).contains l := by
  obtain ⟨h1, h2⟩ := labOf_valid a f hf
  obtain ⟨h3, h4⟩ := labOf_valid b f hf
  rw [labOf_eq, labOf_eq, meets_eq h1 h2 h3 h4, tcrLabsOf_tkCd, tcrLabsOf_tkCd]

@[expose] def c1Flags (bl : ℕ) : List ℕ := if bl = 2 then [2] else [1, 3]

@[expose] def c1Eps (bl : ℕ) : ℤ := if bl = 0 then 1 else -1

theorem allowed_imp {bl f dJ dx : ℕ} (h : allowed bl f dJ dx = true) :
    tcrAllowedC1 (c1Eps bl) f (tkCd dJ) (tkCd dx) = true := by
  simp only [allowed, brecB_eq, nbeq_eq, andB_eq, orB_eq] at h
  by_cases h0 : bl = 0
  · subst h0
    simp only [decide_true, cond_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨rfl, (⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩)⟩ := h <;> decide
  · by_cases h2 : bl = 2
    · subst h2
      have h20 : ((2 : ℕ) = 0) = False := by decide
      simp only [h20, decide_false, cond_false,
        decide_true, cond_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
      obtain ⟨rfl, rfl, rfl | rfl⟩ := h <;> simp only [c1Eps] <;> decide
    · simp only [h0, h2, decide_false, cond_false, Bool.and_eq_true, decide_eq_true_eq,
        Bool.or_eq_true] at h
      obtain ⟨rfl, rfl, rfl | rfl | rfl⟩ := h <;> simp only [c1Eps, h0, if_false] <;> decide

theorem jok_spec {bl psJ dJ : ℕ} {ps ds : ℕ → ℕ} (h : jok bl psJ dJ ps ds = true) :
    ∀ f ∈ c1Flags bl, ∀ x < 4, ps x ≠ psJ →
      (tcrLabsOf (tkCd (ds x)) f).any (tcrSplitT 3) = true →
      (∀ y < 4, y ≠ x →
        (tcrLabsOf (tkCd (ds y)) f).any (fun l => (tcrLabsOf (tkCd dJ) f).contains l) = true ∨
        (tcrLabsOf (tkCd (ds y)) f).any (tcrHalfSplitT 3) = true) →
      tcrAllowedC1 (c1Eps bl) f (tkCd dJ) (tkCd (ds x)) = true := by
  intro f hf x hx hps hsp hoth
  have hX : jokX bl f psJ dJ ps ds x = true := by
    simp only [jok, brecB_eq, nbeq_eq, andB_eq, Bool.and_eq_true] at h
    by_cases h2 : bl = 2
    · subst h2
      simp only [c1Flags, if_true, List.mem_singleton] at hf
      subst hf
      simp only [decide_true, cond_true] at h
      exact (allLt_iff _ _).1 h x hx
    · simp only [c1Flags, h2, if_false, List.mem_cons, List.mem_nil_iff, or_false] at hf
      simp only [h2, decide_false, cond_false, Bool.and_eq_true] at h
      rcases hf with rfl | rfl
      · exact (allLt_iff _ _).1 h.1 x hx
      · exact (allLt_iff _ _).1 h.2 x hx
  have hf3 : f ≤ 3 := by
    unfold c1Flags at hf
    split_ifs at hf <;> simp at hf <;> omega
  simp only [jokX, strictB_eq, orB_eq, notB_eq, andB_eq, nbeq_eq] at hX
  rw [anyLab_labOf split3 (tcrSplitT 3) (fun l hl => split3_eq hl) _ _ hf3, hsp] at hX
  have hall : allLt 4 (fun y => decide (y = x) ||
      (meets (labOf (ds y) f) (labOf dJ f) || anyLab half3 (labOf (ds y) f))) = true := by
    rw [allLt_iff]
    intro y hy
    by_cases hyx : y = x
    · simp [hyx]
    · rw [meets_labOf _ _ _ hf3, anyLab_labOf half3 (tcrHalfSplitT 3) (fun l hl => half3_eq hl) _ _ hf3]
      rcases hoth y hy hyx with h1 | h1 <;> simp only [h1, Bool.or_true, Bool.true_or]
  simp only [hps, decide_false, Bool.not_false, Bool.true_and] at hX
  rw [hall] at hX
  exact allowed_imp (by simpa using hX)

theorem labK_eq (d k f : ℕ) :
    labK d k f = tkLab (tcrComponentLabel (tkCd5 d).r (tkCd5 d).N (tkKind k) ((tkCd5 d).e * f)) :=
  compLab_eq _ _ _ _

theorem labK_valid (d k f : ℕ) (hf : f ≤ 5) :
    (tcrComponentLabel (tkCd5 d).r (tkCd5 d).N (tkKind k) ((tkCd5 d).e * f)).r < 16 ∧
    (tcrComponentLabel (tkCd5 d).r (tkCd5 d).N (tkKind k) ((tkCd5 d).e * f)).n < 2 ^ 30 := by
  obtain ⟨h1, h2⟩ := compLab_valid (tkCd5 d).r (tkCd5 d).N (tkKind k) ((tkCd5 d).e * f)
    (dR_lt d)
  refine ⟨h1, ?_⟩
  rw [h2]
  have := dE_lt d
  change dE d * f < _
  nlinarith

theorem any_tkKs (m : ℕ) (P : TcrKind → Bool) :
    (tkKs m).any P = anyLt 4 (fun k => bit m k && P (tkKind k)) := by
  rw [Bool.eq_iff_iff, anyLt_iff, List.any_eq_true]
  simp only [tkKs, List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨_, ⟨k, ⟨hk, hb⟩, rfl⟩, hP⟩
    exact ⟨k, hk, hb, hP⟩
  · rintro ⟨k, hk, hb, hP⟩
    exact ⟨_, ⟨k, ⟨hk, hb⟩, rfl⟩, hP⟩

theorem anyLabK_eq (q : ℕ → Bool) (q' : TcrLab → Bool)
    (hq : ∀ l : TcrLab, l.r < 16 → q (tkLab l) = q' l) (d f : ℕ) (hf : f ≤ 5) :
    anyLabK q d f = (tcrLabsOf (tkCd5 d) f).any q' := by
  rw [anyLabK, tcrLabsOf, List.any_flatMap]
  change _ = (tkKs (dKs d)).any _
  rw [any_tkKs]
  congr 1
  funext k
  rw [andB_eq]
  congr 1
  obtain ⟨h1, h2⟩ := labK_valid d k f hf
  rw [labK_eq, anyLab_eq q h1 h2]
  exact any_congr' fun m hm => hq m (class_r h1 hm)

theorem meetsK_eq (a b f : ℕ) (hf : f ≤ 5) :
    meetsK a b f = (tcrLabsOf (tkCd5 a) f).any fun l => (tcrLabsOf (tkCd5 b) f).contains l := by
  have ha : tcrLabsOf (tkCd5 a) f = (tkKs (dKs a)).flatMap fun k =>
      tcrLabelClass (tcrComponentLabel (tkCd5 a).r (tkCd5 a).N k ((tkCd5 a).e * f)) := rfl
  have hb : ∀ l, (tcrLabsOf (tkCd5 b) f).contains l = true ↔ ∃ k' < 4, bit (dKs b) k' = true ∧
      l ∈ tcrLabelClass (tcrComponentLabel (tkCd5 b).r (tkCd5 b).N (tkKind k')
        ((tkCd5 b).e * f)) := by
    intro l
    have hb' : tcrLabsOf (tkCd5 b) f = (tkKs (dKs b)).flatMap fun k =>
        tcrLabelClass (tcrComponentLabel (tkCd5 b).r (tkCd5 b).N k ((tkCd5 b).e * f)) := rfl
    rw [hb', List.contains_iff_mem, List.mem_flatMap]
    constructor
    · rintro ⟨kd, hkd, hl⟩
      simp only [tkKs, List.mem_map, List.mem_filter, List.mem_range] at hkd
      obtain ⟨k', ⟨hk', hbk⟩, rfl⟩ := hkd
      exact ⟨k', hk', hbk, hl⟩
    · rintro ⟨k', hk', hbk, hl⟩
      refine ⟨tkKind k', ?_, hl⟩
      simp only [tkKs, List.mem_map, List.mem_filter, List.mem_range]
      exact ⟨k', ⟨hk', hbk⟩, rfl⟩
  rw [meetsK, ha, List.any_flatMap, any_tkKs]
  congr 1
  funext k
  rw [andB_eq]
  congr 1
  rw [Bool.eq_iff_iff, anyLt_iff, List.any_eq_true]
  obtain ⟨h1, h2⟩ := labK_valid a k f hf
  simp only [andB_eq, Bool.and_eq_true]
  have key : ∀ k', meets (labK a k f) (labK b k' f) =
      (tcrLabelClass (tcrComponentLabel (tkCd5 a).r (tkCd5 a).N (tkKind k) ((tkCd5 a).e * f))).any
        fun l => (tcrLabelClass (tcrComponentLabel (tkCd5 b).r (tkCd5 b).N (tkKind k')
          ((tkCd5 b).e * f))).contains l := fun k' => by
    obtain ⟨h3, h4⟩ := labK_valid b k' f hf
    rw [labK_eq, labK_eq, meets_eq h1 h2 h3 h4]
  simp only [key, List.any_eq_true, List.contains_iff_mem, hb]
  constructor
  · rintro ⟨k', hk', hbk, l, hl, hl'⟩
    exact ⟨l, hl, k', hk', hbk, hl'⟩
  · rintro ⟨l, hl, k', hk', hbk, hl'⟩
    exact ⟨k', hk', hbk, l, hl, hl'⟩

theorem bit_flags (b0 b1 b2 b3 b4 b5 : Bool) :
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 0 = b0 ∧
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 1 = b1 ∧
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 2 = b2 ∧
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 3 = b3 ∧
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 4 = b4 ∧
    bit (b2n b0 + (2 * b2n b1 + (4 * b2n b2 + (8 * b2n b3 + (16 * b2n b4 + 32 * b2n b5))))) 5 = b5 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

@[expose] def c2Flags (s : ℕ) : List ℕ := if s = 1 then [3] else [1, 5]

theorem jok5_spec {s psJ dJ : ℕ} {ps ds fs : ℕ → ℕ} (hfs : ∀ y < 6, fs y = flags5 (ds y))
    (h : jok5 s psJ dJ ps ds fs = true) :
    ∀ f ∈ c2Flags s, ∀ x < 6, ps x ≠ psJ →
      (tcrLabsOf (tkCd5 (ds x)) f).any (tcrSplitT 5) = true →
      (∀ y < 6, y ≠ x →
        (tcrLabsOf (tkCd5 (ds y)) f).any (fun l => (tcrLabsOf (tkCd5 dJ) f).contains l) = true ∨
        (tcrLabsOf (tkCd5 (ds y)) f).any (tcrHalfSplitT 5) = true) → False := by
  intro f hf x hx hps hsp hoth
  obtain ⟨fi, hfi, hX⟩ : ∃ fi, fi < 3 ∧ f = 2 * fi + 1 ∧ jok5X f fi psJ dJ ps ds fs x = true := by
    simp only [jok5, brecB_eq, nbeq_eq, andB_eq, Bool.and_eq_true] at h
    by_cases h1 : s = 1
    · subst h1
      simp only [c2Flags, if_true, List.mem_singleton] at hf
      subst hf
      simp only [decide_true, cond_true] at h
      exact ⟨1, by norm_num, rfl, (allLt_iff _ _).1 h x hx⟩
    · simp only [c2Flags, h1, if_false, List.mem_cons, List.mem_nil_iff, or_false] at hf
      simp only [h1, decide_false, cond_false, Bool.and_eq_true] at h
      rcases hf with rfl | rfl
      · exact ⟨0, by norm_num, rfl, (allLt_iff _ _).1 h.1 x hx⟩
      · exact ⟨2, by norm_num, rfl, (allLt_iff _ _).1 h.2 x hx⟩
  obtain ⟨rfl, hX⟩ := hX
  have hf5 : 2 * fi + 1 ≤ 5 := by omega
  have hsplit : ∀ d, bit (flags5 d) (2 * fi) = anyLabK (splitP 5) d (2 * fi + 1) := by
    intro d
    obtain ⟨e0, -, e2, -, e4, -⟩ := bit_flags (anyLabK (splitP 5) d 1) (anyLabK (halfP 5) d 1)
      (anyLabK (splitP 5) d 3) (anyLabK (halfP 5) d 3) (anyLabK (splitP 5) d 5)
      (anyLabK (halfP 5) d 5)
    interval_cases fi
    · exact e0
    · exact e2
    · exact e4
  have hhalf : ∀ d, bit (flags5 d) (2 * fi + 1) = anyLabK (halfP 5) d (2 * fi + 1) := by
    intro d
    obtain ⟨-, e1, -, e3, -, e5⟩ := bit_flags (anyLabK (splitP 5) d 1) (anyLabK (halfP 5) d 1)
      (anyLabK (splitP 5) d 3) (anyLabK (halfP 5) d 3) (anyLabK (splitP 5) d 5)
      (anyLabK (halfP 5) d 5)
    interval_cases fi
    · exact e1
    · exact e3
    · exact e5
  simp only [jok5X, notB_eq, andB_eq, orB_eq, nbeq_eq, nmul_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff] at hX
  rcases hX with hX | hX | hX
  · simp [hps] at hX
  · rw [hfs x hx, hsplit, anyLabK_eq (splitP 5) (tcrSplitT 5) (fun l hl => splitP_eq 5 hl) _ _
      hf5, hsp] at hX
    exact Bool.false_ne_true hX.symm
  · have : allLt 6 (fun y => decide (y = x) ||
        (bit (fs y) (Nat.succ (2 * fi)) || meetsK (ds y) dJ (2 * fi + 1))) = true := by
      rw [allLt_iff]
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · rw [hfs y hy, Nat.succ_eq_add_one, hhalf,
          anyLabK_eq (halfP 5) (tcrHalfSplitT 5) (fun l hl => halfP_eq 5 hl) _ _ hf5,
          meetsK_eq _ _ _ hf5]
        rcases hoth y hy hyx with h1 | h1 <;> simp only [h1, Bool.or_true, Bool.true_or]
    rw [this] at hX
    exact Bool.false_ne_true hX.symm

end CFSG.KC.TcRes

end
