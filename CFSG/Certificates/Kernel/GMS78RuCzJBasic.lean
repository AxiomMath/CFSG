module

public import Certificates.Data.Kernel.GMS78RuCzJ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETableDefs
public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.RankThree.Native.DerivedGenerators
public import Certificates.Data.GMS78RuCzJCert
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
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

namespace CFSG.KC.GMS.CzJ

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.GMS
open CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSporadicStandard.Fin76b.AutETable (mt ix tab ev)

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem neStrictB_eq (y : Nat) (k : Nat → Bool) : neStrictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

private theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · simp [Nat.ne_of_beq_eq_false h]
  · simp [Nat.eq_of_beq_eq_true h]

private theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    intro hl
    have := Nat.blt_eq.mpr hl
    rw [h] at this
    exact Bool.false_ne_true this
  · simp [Nat.blt_eq.mp h]

private theorem nIf (c : Bool) (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem pw2_eq (w : Nat) : pw2 w = 2 ^ w := by
  simp [pw2, Nat.shiftLeft_eq]

private theorem maskN_eq (w : Nat) : maskN w = 2 ^ w - 1 := by
  simp [maskN, pw2_eq]

theorem neAllL_iff {α : Type} {p : α → Bool} {l : List α} :
    neAllL p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | cons a l ih =>
    change andB (p a) (neAllL p l) = true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

theorem neLen_eq {α : Type} (l : List α) : neLen l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change strictN (neLen l) Nat.succ = _
    rw [strictN_eq', ih]
    rfl

theorem neGet_eq {α : Type} (d : α) (l : List α) (k : Nat) : neGet d l k = l.getD k d := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k =>
      change neGet d l k = _
      rw [ih, List.getD_cons_succ]

theorem allN_iff' {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem fget_eq' (X i w : Nat) : fget X i w = X / 2 ^ (i * w) % 2 ^ w := by
  change (X >>> (i * w)) &&& maskN w = _
  rw [maskN_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem fget11_lt (X i : Nat) : fget X i 11 < 2048 := by
  rw [fget_eq']
  exact Nat.mod_lt _ (by decide)

private theorem fget_zero (i w : Nat) : fget 0 i w = 0 := by
  simp [fget_eq']

private theorem testBit_fget (X i w j : Nat) :
    (fget X i w).testBit j = (decide (j < w) && X.testBit (i * w + j)) := by
  change ((X >>> (i * w)) &&& maskN w).testBit j = _
  rw [maskN_eq, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

private theorem testBit_lt11 {v b : Nat} (hv : v < 2048) (hb : 11 ≤ b) : v.testBit b = false :=
  Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hv
    (Nat.le_trans (by decide : 2048 ≤ 2 ^ 11) (Nat.pow_le_pow_right (by decide) hb)))

private theorem fget_lor_shl {X v a : Nat} (hv : v < 2048) (hX : fget X a 11 = 0) (j : Nat) :
    fget (X ||| v <<< (11 * a)) j 11 = if j = a then v else fget X j 11 := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [testBit_fget, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hb : b < 11
  · by_cases hj : j = a
    · subst hj
      rw [if_pos rfl]
      have h1 : X.testBit (j * 11 + b) = false := by
        have := congrArg (fun x => x.testBit b) hX
        simp only [testBit_fget, Nat.zero_testBit] at this
        simpa [hb] using this
      rw [h1, show j * 11 + b - 11 * j = b by omega]
      simp [hb, show 11 * j ≤ j * 11 + b by omega]
    · rw [if_neg hj, testBit_fget]
      have : (decide (j * 11 + b ≥ 11 * a) && v.testBit (j * 11 + b - 11 * a)) = false := by
        rcases Nat.lt_or_gt_of_ne hj with h | h
        · have : ¬ j * 11 + b ≥ 11 * a := by omega
          simp [this]
        · rw [testBit_lt11 hv (by omega)]
          simp
      rw [this, Bool.or_false]
  · have hb' : decide (b < 11) = false := by simp [hb]
    rw [hb', Bool.false_and]
    split
    · exact (testBit_lt11 hv (by omega)).symm
    · rw [testBit_fget, hb', Bool.false_and]

private def pv : List Nat → Nat
  | [] => 0
  | x :: l => x + 2048 * pv l

private theorem czPack_aux : ∀ l : List Nat, (∀ x ∈ l, x < 2048) → ∀ s,
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 11))) l s = pv l <<< s
  | [], _, s => by
    change 0 = 0 <<< s
    rw [Nat.zero_shiftLeft]
  | x :: l, hl, s => by
    change Nat.lor (Nat.shiftLeft x s) (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 11))) l (Nat.add s 11)) = _
    rw [czPack_aux l (fun y hy => hl y (List.mem_cons_of_mem _ hy))]
    have hx : x < 2 ^ 11 := hl x List.mem_cons_self
    change x <<< s ||| pv l <<< (s + 11) = (x + 2048 * pv l) <<< s
    rw [Nat.add_comm s 11, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt hx]
    congr 1
    rw [Nat.shiftLeft_eq, show (2 : Nat) ^ 11 = 2048 from rfl]
    omega

private theorem pv_field : ∀ l : List Nat, (∀ x ∈ l, x < 2048) → ∀ i,
    pv l / 2 ^ (i * 11) % 2 ^ 11 = l.getD i 0
  | [], _, i => by simp [pv]
  | x :: l, hl, 0 => by
    have hx := hl x List.mem_cons_self
    simp only [pv, Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
    rw [show (2 : Nat) ^ 11 = 2048 from rfl]
    omega
  | x :: l, hl, i + 1 => by
    have hx := hl x List.mem_cons_self
    rw [List.getD_cons_succ, ← pv_field l (fun y hy => hl y (List.mem_cons_of_mem _ hy)) i,
      show (i + 1) * 11 = 11 + i * 11 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    congr 2
    simp only [pv]
    rw [show (2 : Nat) ^ 11 = 2048 from rfl]
    omega

private theorem czPack_pv {l : List Nat} (hl : ∀ x ∈ l, x < 2048) : czPack l = pv l :=
  (czPack_aux l hl 0).trans Nat.shiftLeft_zero

theorem czPack_fget {l : List Nat} (hl : ∀ x ∈ l, x < 2048) (i : Nat) :
    fget (czPack l) i 11 = l.getD i 0 := by
  rw [czPack_pv hl, fget_eq', pv_field l hl]

theorem czPack_inj {l l' : List Nat} (hl : ∀ x ∈ l, x < 2048) (hl' : ∀ x ∈ l', x < 2048)
    (hlen : l.length = l'.length) (h : czPack l = czPack l') : l = l' := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have e := congrArg (fun X => fget X i 11) h
  simp only [czPack_fget hl, czPack_fget hl'] at e
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at e

private theorem czEv_aux (RW : Nat → Nat) (INV T : Nat) : ∀ (w : List Nat) (acc : Nat),
    acc < 2048 → List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
      (fun l _ ih acc => strictN (czMt RW acc (czLet INV T l)) ih) w acc < 2048
  | [], _, h => h
  | l :: w, acc, _ => by
    change strictN (czMt RW acc (czLet INV T l)) (List.rec (motive := fun _ => Nat → Nat)
      (fun acc => acc) (fun l _ ih acc => strictN (czMt RW acc (czLet INV T l)) ih) w) < 2048
    rw [strictN_eq']
    exact czEv_aux RW INV T w _ (fget11_lt _ _)

theorem czEv_lt (RW : Nat → Nat) (INV T : Nat) (w : List Nat) : czEv RW INV T w < 2048 :=
  czEv_aux RW INV T w 0 (by decide)

private theorem czEvs_aux (f : List Nat → Nat) : ∀ (ws : List (List Nat)) (s : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun w _ ih s => Nat.lor (Nat.shiftLeft (f w) s) (ih (Nat.add s 11))) ws s =
    List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
      (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 11))) (ws.map f) s
  | [], _ => rfl
  | w :: ws, s => congrArg (Nat.lor (Nat.shiftLeft (f w) s)) (czEvs_aux f ws (Nat.add s 11))

theorem czEvs_eq (RW : Nat → Nat) (INV T : Nat) (ws : List (List Nat)) :
    czEvs RW INV T ws = czPack (ws.map (czEv RW INV T)) :=
  czEvs_aux (czEv RW INV T) ws 0

private noncomputable def tabL (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => Nat.lor S (Nat.shiftLeft (f i) (Nat.mul 11 i))) n

private theorem tabL_succ (f : Nat → Nat) (n : Nat) :
    tabL f (n + 1) = tabL f n ||| f n <<< (11 * n) :=
  strictN_eq' (tabL f n) fun S => Nat.lor S (Nat.shiftLeft (f n) (Nat.mul 11 n))

private theorem tabL_spec {f : Nat → Nat} (hf : ∀ i < 2048, f i < 2048) :
    ∀ n ≤ 2048, ∀ j, fget (tabL f n) j 11 = if j < n then f j else 0
  | 0, _, j => fget_zero _ _
  | n + 1, hn, j => by
    have ih := tabL_spec hf n (by omega)
    rw [tabL_succ, fget_lor_shl (hf n (by omega)) (by rw [ih, if_neg (Nat.lt_irrefl _)]), ih]
    by_cases hj : j = n
    · rw [if_pos hj, if_pos (by omega), hj]
    · rw [if_neg hj]
      by_cases hj' : j < n
      · rw [if_pos hj', if_pos (by omega)]
      · rw [if_neg hj', if_neg (by omega)]

theorem czTab_fget {f : Nat → Nat} (hf : ∀ i < 2048, f i < 2048) {i : Nat} (hi : i < 2048) :
    fget (czTab f) i 11 = f i := by
  change fget (tabL f 2048) i 11 = f i
  rw [tabL_spec hf 2048 (Nat.le_refl _), if_pos hi]

private theorem filt_aux (p : Nat → Bool) : ∀ (n : Nat) (acc : List Nat),
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i)))
      n acc = (List.range n).filter p ++ acc
  | 0, acc => by simp
  | n + 1, acc => by
    change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons i acc) (p i))) n
      (Bool.rec (motive := fun _ => List Nat) acc (List.cons n acc) (p n)) = _
    rw [filt_aux p n, List.range_succ, List.filter_append, List.append_assoc]
    cases h : p n <;> simp [h]

theorem czFilter_eq (p : Nat → Bool) : czFilter p = (List.range 2048).filter p :=
  (filt_aux p 2048 []).trans (List.append_nil _)

theorem czListEq_iff {a b : List Nat} : czListEq a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y ys => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
  | cons x xs ih =>
    cases b with
    | nil => exact ⟨fun h => Bool.noConfusion h, fun h => nomatch h⟩
    | cons y ys =>
      change andB (Nat.beq x y) (czListEq xs ys) = true ↔ _
      rw [andB_iff, ih, List.cons.injEq, beq_dec, decide_eq_true_eq]

theorem czAny_eq (p : Nat → Bool) (l : List Nat) : czAny p l = l.any p := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change orB (p x) (czAny p l) = _
    rw [orB_eq, ih, List.any_cons]

private theorem conjs_aux (g : Nat → Nat) : ∀ (n : Nat) (acc : List Nat),
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (List.cons (g i) acc)) n acc = (List.range n).map g ++ acc
  | 0, acc => by simp
  | n + 1, acc => by
    change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun i ih acc => ih (List.cons (g i) acc)) n (g n :: acc) = _
    rw [conjs_aux g n, List.range_succ, List.map_append, List.append_assoc]
    rfl

theorem czConjTs_eq (RW : Nat → Nat) (INV : Nat) (GI : List Nat) :
    czConjTs RW INV GI = (List.range 2048).map (czConjT RW INV GI) :=
  (conjs_aux (czConjT RW INV GI) 2048 []).trans (List.append_nil _)

theorem czPtsK_spec {PT : Nat → Nat} : ∀ {l : List Nat} {i : Nat}, czPtsK PT l i = true →
    ∀ j (hj : j < l.length), PT (i + j) = l[j]
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | u :: l, i, h, j, hj => by
    change andB (Nat.beq (PT i) u) (neStrictB (Nat.succ i) (czPtsK PT l)) = true at h
    rw [andB_iff, neStrictB_eq] at h
    cases j with
    | zero => exact Nat.eq_of_beq_eq_true h.1
    | succ j =>
      rw [show i + (j + 1) = (i + 1) + j by omega]
      exact czPtsK_spec h.2 j (by simpa using hj)

theorem czColsK_spec {LK : Nat → Nat} : ∀ {l : List (Array Nat)} {i : Nat}, czColsK LK l i = true →
    ∀ j (hj : j < l.length), l[j].size = 6 ∧ ∀ k < 6, fget (LK k) (i + j) 11 = l[j].getD k 0
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | e :: l, i, h, j, hj => by
    change andB (Nat.beq e.size 6) (andB (allN 6 fun k => Nat.beq (fget (LK k) i 11) (e.getD k 0))
      (neStrictB (Nat.succ i) (czColsK LK l))) = true at h
    rw [andB_iff, andB_iff, allN_iff', neStrictB_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    cases j with
    | zero =>
      exact ⟨Nat.eq_of_beq_eq_true h1, fun k hk => Nat.eq_of_beq_eq_true (h2 k hk)⟩
    | succ j =>
      rw [show i + (j + 1) = (i + 1) + j by omega]
      exact czColsK_spec h3 j (by simpa using hj)

theorem czFieldsK_spec {w F : Nat} : ∀ {l : List Nat} {i : Nat}, czFieldsK w F l i = true →
    ∀ j (hj : j < l.length), fget F (i + j) w = l[j]
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | x :: l, i, h, j, hj => by
    change andB (Nat.beq (fget F i w) x) (neStrictB (Nat.succ i) (czFieldsK w F l)) = true at h
    rw [andB_iff, neStrictB_eq] at h
    cases j with
    | zero => exact Nat.eq_of_beq_eq_true h.1
    | succ j =>
      rw [show i + (j + 1) = (i + 1) + j by omega]
      exact czFieldsK_spec h.2 j (by simpa using hj)

private theorem bitset_spec (κ : Nat → Nat) (c : Nat → Prop) [DecidablePred c] (S : Nat → Nat)
    (h0 : S 0 = 0)
    (hs : ∀ i, S (i + 1) = if c i ∧ S i &&& 2 ^ (κ i + 1) = 0 then S i ||| 2 ^ (κ i + 1)
      else S i ||| 1) :
    ∀ n, (S n).testBit 0 = false →
      (∀ i < n, ∀ j < n, κ i = κ j → i = j) ∧
        (∀ m, (S n).testBit (m + 1) = true ↔ ∃ j < n, κ j = m)
  | 0, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun m => by
      rw [h0, Nat.zero_testBit]
      exact ⟨fun h => Bool.noConfusion h, fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _)⟩⟩
  | n + 1, hn => by
    rw [hs] at hn
    split at hn
    · rename_i hc
      have hn' : (S n).testBit 0 = false := by
        rw [Nat.testBit_or, Nat.testBit_two_pow] at hn
        simpa using hn
      obtain ⟨hinj, hbit⟩ := bitset_spec κ c S h0 hs n hn'
      have hnew : ∀ j < n, κ j ≠ κ n := by
        intro j hj e
        have h1 : (S n).testBit (κ n + 1) = true := (hbit _).2 ⟨j, hj, e⟩
        have h2 := congrArg (fun x => x.testBit (κ n + 1)) hc.2
        simp only [Nat.testBit_and, Nat.testBit_two_pow_self, h1, Nat.zero_testBit] at h2
        exact Bool.noConfusion h2
      refine ⟨fun i hi j hj e => ?_, fun m => ?_⟩
      · rcases (by omega : i < n ∨ i = n) with hi' | hi' <;>
          rcases (by omega : j < n ∨ j = n) with hj' | hj'
        · exact hinj i hi' j hj' e
        · subst hj'; exact absurd e (hnew i hi')
        · subst hi'; exact absurd e.symm (hnew j hj')
        · omega
      · rw [hs, if_pos hc, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, hbit,
          decide_eq_true_eq]
        constructor
        · rintro (⟨j, hj, e⟩ | h)
          · exact ⟨j, by omega, e⟩
          · exact ⟨n, by omega, by omega⟩
        · rintro ⟨j, hj, e⟩
          rcases (by omega : j < n ∨ j = n) with hj' | hj'
          · exact Or.inl ⟨j, hj', e⟩
          · subst hj'; exact Or.inr (by omega)
    · rw [Nat.testBit_or] at hn
      simp at hn

private theorem bit0_of_land {X : Nat} (h : X &&& 1 = 0) : X.testBit 0 = false := by
  have := congrArg (fun x => x.testBit 0) h
  simpa [Nat.testBit_and] using this

private noncomputable def keysL (PT : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => (fun b => Bool.rec (motive := fun _ => Nat) (Nat.lor S 1)
        (Nat.lor S b) (Nat.beq (Nat.land S b) 0)) (pw2 (Nat.succ (czKey (PT i))))) n

private theorem keysL_succ (PT : Nat → Nat) (i : Nat) :
    keysL PT (i + 1) = if True ∧ keysL PT i &&& 2 ^ (czKey (PT i) + 1) = 0 then
      keysL PT i ||| 2 ^ (czKey (PT i) + 1) else keysL PT i ||| 1 := by
  refine (strictN_eq' (keysL PT i) fun S => (fun b => Bool.rec (motive := fun _ => Nat)
    (Nat.lor S 1) (Nat.lor S b) (Nat.beq (Nat.land S b) 0)) (pw2 (Nat.succ (czKey (PT i))))).trans ?_
  simp only [nIf, beq_dec, pw2_eq, decide_eq_true_eq, true_and]
  rfl

theorem kKeys_spec {PT : Nat → Nat} (h : kKeys PT = true) :
    ∀ i < 2048, ∀ j < 2048, czKey (PT i) = czKey (PT j) → i = j := by
  have h1 : keysL PT 2048 &&& 1 = 0 := Nat.eq_of_beq_eq_true h
  exact (bitset_spec (fun i => czKey (PT i)) (fun _ => True) (keysL PT) rfl (keysL_succ PT)
    2048 (bit0_of_land h1)).1

private noncomputable def injL (K : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => (fun v => Bool.rec (motive := fun _ => Nat) (Nat.lor S 1)
        (Nat.lor S (pw2 (Nat.succ v))) (andB (Nat.blt v 2048)
          (Nat.beq (Nat.land S (pw2 (Nat.succ v))) 0)))
      (fget K i 11)) n

private theorem injL_succ (K : Nat) (i : Nat) :
    injL K (i + 1) = if fget K i 11 < 2048 ∧ injL K i &&& 2 ^ (fget K i 11 + 1) = 0 then
      injL K i ||| 2 ^ (fget K i 11 + 1) else injL K i ||| 1 := by
  refine (strictN_eq' (injL K i) fun S => (fun v => Bool.rec (motive := fun _ => Nat)
    (Nat.lor S 1) (Nat.lor S (pw2 (Nat.succ v))) (andB (Nat.blt v 2048)
      (Nat.beq (Nat.land S (pw2 (Nat.succ v))) 0))) (fget K i 11)).trans ?_
  simp only [nIf, andB_eq, beq_dec, blt_dec, pw2_eq, Bool.and_eq_true, decide_eq_true_eq]
  rfl

theorem czInj_spec {K : Nat} (h : czInj K = true) :
    ∀ i < 2048, ∀ j < 2048, fget K i 11 = fget K j 11 → i = j := by
  have h1 : injL K 2048 &&& 1 = 0 := Nat.eq_of_beq_eq_true h
  exact (bitset_spec (fun i => fget K i 11) (fun i => fget K i 11 < 2048) (injL K) rfl
    (injL_succ K) 2048 (bit0_of_land h1)).1

private noncomputable def invL (K : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i S => strictN S fun S => Nat.lor S (Nat.shiftLeft i (Nat.mul 11 (fget K i 11)))) n

private theorem invL_succ (K : Nat) (n : Nat) :
    invL K (n + 1) = invL K n ||| n <<< (11 * fget K n 11) :=
  strictN_eq' (invL K n) fun S => Nat.lor S (Nat.shiftLeft n (Nat.mul 11 (fget K n 11)))

private theorem invL_spec {K : Nat}
    (hinj : ∀ i < 2048, ∀ j < 2048, fget K i 11 = fget K j 11 → i = j) :
    ∀ n ≤ 2048, (∀ i < n, fget (invL K n) (fget K i 11) 11 = i) ∧
      (∀ j, (∀ i < n, fget K i 11 ≠ j) → fget (invL K n) j 11 = 0)
  | 0, _ => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => fget_zero _ _⟩
  | n + 1, hn => by
    obtain ⟨h1, h2⟩ := invL_spec hinj n (by omega)
    have hz : fget (invL K n) (fget K n 11) 11 = 0 :=
      h2 _ fun i hi e => by have := hinj i (by omega) n (by omega) e; omega
    have hv : n < 2048 := by omega
    rw [invL_succ]
    refine ⟨fun i hi => ?_, fun j hj => ?_⟩
    · rw [fget_lor_shl hv hz]
      rcases (by omega : i < n ∨ i = n) with hi' | hi'
      · rw [if_neg (fun e => by have := hinj i (by omega) n (by omega) e; omega), h1 i hi']
      · rw [if_pos (by rw [hi']), hi']
    · rw [fget_lor_shl hv hz, if_neg (fun e => hj n (by omega) e.symm),
        h2 j (fun i hi => hj i (by omega))]

theorem czInvT_fget {K : Nat} (h : czInj K = true) :
    ∀ i < 2048, fget (czInvT K) (fget K i 11) 11 = i :=
  (invL_spec (czInj_spec h) 2048 (Nat.le_refl _)).1

private noncomputable def hv (RW : Nat → Nat) (PAR LAB T : Nat) (f a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih a => Bool.rec (motive := fun _ => Nat)
      (czMt RW (fget T (fget LAB a 3) 11) (ih (fget PAR a 11))) 0 (Nat.beq a 0)) f a

private theorem hv_succ (RW : Nat → Nat) (PAR LAB T f a : Nat) :
    hv RW PAR LAB T (f + 1) a =
      if a = 0 then 0 else czMt RW (fget T (fget LAB a 3) 11) (hv RW PAR LAB T f (fget PAR a 11)) := by
  show Bool.rec (motive := fun _ => Nat)
    (czMt RW (fget T (fget LAB a 3) 11) (hv RW PAR LAB T f (fget PAR a 11))) 0 (Nat.beq a 0) = _
  rw [nIf, beq_dec]
  simp only [decide_eq_true_eq]

private theorem hv_fuel {RW : Nat → Nat} {PAR LAB T : Nat}
    (hpar : ∀ a < 2048, 0 < a → fget PAR a 11 < a) :
    ∀ f g a, a < f → a < g → a < 2048 → hv RW PAR LAB T f a = hv RW PAR LAB T g a
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, g + 1, a, hf, hg, ha => by
    rw [hv_succ, hv_succ]
    by_cases h0 : a = 0
    · rw [if_pos h0, if_pos h0]
    · have hp := hpar a ha (by omega)
      rw [if_neg h0, if_neg h0, hv_fuel (RW := RW) (LAB := LAB) (T := T) hpar f g _ (by omega) (by omega) (by omega)]

private noncomputable def homL (RW : Nat → Nat) (PAR LAB T : Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun a H => strictN H fun H =>
    Bool.rec (motive := fun _ => Nat)
      (Nat.lor H (Nat.shiftLeft (czMt RW (fget T (fget LAB a 3) 11) (fget H (fget PAR a 11) 11))
        (Nat.mul 11 a))) H (Nat.beq a 0)) n

private theorem homL_succ (RW : Nat → Nat) (PAR LAB T n : Nat) :
    homL RW PAR LAB T (n + 1) = if n = 0 then homL RW PAR LAB T n else
      homL RW PAR LAB T n ||| czMt RW (fget T (fget LAB n 3) 11)
        (fget (homL RW PAR LAB T n) (fget PAR n 11) 11) <<< (11 * n) := by
  refine (strictN_eq' (homL RW PAR LAB T n) fun H => Bool.rec (motive := fun _ => Nat)
    (Nat.lor H (Nat.shiftLeft (czMt RW (fget T (fget LAB n 3) 11) (fget H (fget PAR n 11) 11))
      (Nat.mul 11 n))) H (Nat.beq n 0)).trans ?_
  simp only [nIf, beq_dec, decide_eq_true_eq]
  rfl

private theorem homL_spec {RW : Nat → Nat} {PAR LAB T : Nat}
    (hpar : ∀ a < 2048, 0 < a → fget PAR a 11 < a) :
    ∀ m ≤ 2048, ∀ j, fget (homL RW PAR LAB T m) j 11 =
      if j < m then hv RW PAR LAB T 2048 j else 0
  | 0, _, j => fget_zero _ _
  | m + 1, hm, j => by
    have ih := homL_spec (RW := RW) (LAB := LAB) (T := T) hpar m (by omega)
    rw [homL_succ]
    by_cases h0 : m = 0
    · subst h0
      rw [if_pos rfl, ih]
      by_cases hj : j = 0
      · subst hj
        rw [if_neg (Nat.lt_irrefl _), if_pos (by decide), show 2048 = 2047 + 1 from rfl, hv_succ,
          if_pos rfl]
      · rw [if_neg (Nat.not_lt_zero _), if_neg (by omega)]
    · have hlt : czMt RW (fget T (fget LAB m 3) 11) (fget (homL RW PAR LAB T m) (fget PAR m 11) 11)
          < 2048 := fget11_lt _ _
      have hp := hpar m (by omega) (by omega)
      rw [if_neg h0, fget_lor_shl hlt (by rw [ih, if_neg (Nat.lt_irrefl _)]), ih]
      by_cases hj : j = m
      · subst hj
        have e : hv RW PAR LAB T 2048 j =
            czMt RW (fget T (fget LAB j 3) 11) (hv RW PAR LAB T 2047 (fget PAR j 11)) := by
          have := hv_succ RW PAR LAB T 2047 j
          rw [if_neg h0] at this
          exact this
        rw [if_pos rfl, if_pos (Nat.lt_succ_self _), e,
          hv_fuel (RW := RW) (LAB := LAB) (T := T) hpar 2047 2048 _ (by omega) (by omega)
            (by omega), if_pos hp]
      · rw [if_neg hj, ih]
        by_cases hj' : j < m
        · rw [if_pos hj', if_pos (by omega)]
        · rw [if_neg hj', if_neg (by omega)]

theorem czHom_fget {RW : Nat → Nat} {PAR LAB : Nat} (T : Nat)
    (hpar : ∀ a < 2048, 0 < a → fget PAR a 11 < a) :
    ∀ a < 2048, fget (czHom RW PAR LAB T) a 11 = czHomVal RW PAR LAB T a := by
  intro a ha
  change fget (homL RW PAR LAB T 2048) a 11 = hv RW PAR LAB T 2048 a
  rw [homL_spec hpar 2048 (Nat.le_refl _), if_pos ha]

structure TabI (M : Array (Array Nat)) (inv : Array Nat) (c : ArrCert) (RW : Nat → Nat)
    (PAR LAB INV : Nat) : Prop where
  mt_eq : ∀ a < 2048, ∀ b < 2048, mt M a b = fget (RW a) b 11
  mt_lt : ∀ a b, mt M a b < 2048
  inv_eq : ∀ a < 2048, ix inv a = fget INV a 11
  inv_lt : ∀ a, ix inv a < 2048
  par_eq : ∀ a < 2048, ix c.par a = fget PAR a 11
  lab_eq : ∀ a < 2048, ix c.lab a = fget LAB a 3
  par_lt : ∀ a < 2048, 0 < a → fget PAR a 11 < a
  lab_lt : ∀ a < 2048, 0 < a → fget LAB a 3 < 6

end CFSG.KC.GMS.CzJ

end
