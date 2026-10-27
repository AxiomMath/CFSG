module

public import Certificates.Data.Kernel.Misc.Xi
public import CFSG.Certificates.Kernel.Spor.PK.F4Code
public import CFSG.Certificates.Kernel.Spor.PK.MiscPerm
public import Certificates.Data.CFSGNative.Fischer.HyperovalSearch
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Xi

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46 CFSG.KC.Misc.Lines
  CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73

theorem allIn_iff' {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simpa [Nat.add_sub_cancel' h1] using this
  · intro h ⟨k, hk⟩ _
    simpa using h (lo + k) (by omega) (by omega)

theorem testBit_fold_or (c : Nat → Bool) (f : Nat → Nat) (n j : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => if c i = true then Nat.lor acc (Nat.shiftLeft 1 (f i)) else acc) n).testBit j
        = true ↔ ∃ i < n, c i = true ∧ f i = j := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (if c n = true then Nat.lor (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => if c i = true then Nat.lor acc (Nat.shiftLeft 1 (f i)) else acc) n)
        (Nat.shiftLeft 1 (f n)) else Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => if c i = true then Nat.lor acc (Nat.shiftLeft 1 (f i)) else acc) n).testBit j
        = true ↔ _
    by_cases hc : c n = true
    · rw [if_pos hc, Nat.lor_eq, Nat.testBit_or, Bool.or_eq_true, ih,
        show Nat.shiftLeft 1 (f n) = 2 ^ f n from Nat.one_shiftLeft _,
        Nat.testBit_two_pow, decide_eq_true_iff]
      constructor
      · rintro (⟨i, hi, h1, h2⟩ | h)
        · exact ⟨i, by omega, h1, h2⟩
        · exact ⟨n, by omega, hc, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h1, h2⟩
        · exact Or.inr h2
    · rw [if_neg hc, ih]
      constructor
      · rintro ⟨i, hi, h1, h2⟩
        exact ⟨i, by omega, h1, h2⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h1, h2⟩
        · exact absurd h1 hc

theorem testBit_fold_or_skip (d : Nat → Bool) (f : Nat → Nat) (n j : Nat) :
    (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => if d i = true then acc else Nat.lor acc (Nat.shiftLeft 1 (f i))) n).testBit j
        = true ↔ ∃ i < n, d i = false ∧ f i = j := by
  have := testBit_fold_or (fun i => !d i) f n j
  simp only [Bool.not_eq_true'] at this
  have e : (fun i acc => if d i = true then acc else Nat.lor acc (Nat.shiftLeft 1 (f i))) =
      (fun i acc => if d i = false then Nat.lor acc (Nat.shiftLeft 1 (f i)) else acc) := by
    funext i acc
    cases d i <;> rfl
  rw [e]
  exact this

theorem or_two_pow_of_testBit_true {x p : Nat} (h : x.testBit p = true) : x ||| 2 ^ p = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hi : p = i
  · subst hi
    simp [h]
  · simp [hi]

theorem or_two_pow_of_testBit_false {x p : Nat} (h : x.testBit p = false) :
    x ||| 2 ^ p = x + 2 ^ p := by
  obtain ⟨q, r, hrlt, rfl⟩ : ∃ q r, r < 2 ^ (p + 1) ∧ x = 2 ^ (p + 1) * q + r :=
    ⟨x / 2 ^ (p + 1), x % 2 ^ (p + 1), Nat.mod_lt _ (Nat.two_pow_pos _),
      (Nat.div_add_mod _ _).symm⟩
  rw [Nat.testBit_two_pow_mul_add q hrlt p, if_pos (Nat.lt_succ_self p)] at h
  have hr : r < 2 ^ p := by
    rcases Nat.lt_or_ge r (2 ^ p) with hlt | hge
    · exact hlt
    · exact absurd (Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hge hrlt)
        (by rw [h]; decide)
  have hlt1 : r + 2 ^ p < 2 ^ (p + 1) := by
    rw [Nat.pow_succ]
    omega
  calc (2 ^ (p + 1) * q + r) ||| 2 ^ p
      = ((2 ^ (p + 1) * q) ||| r) ||| 2 ^ p := by rw [← Nat.two_pow_add_eq_or_of_lt hrlt]
    _ = (2 ^ (p + 1) * q) ||| (r ||| 2 ^ p) := Nat.or_assoc _ _ _
    _ = (2 ^ (p + 1) * q) ||| (r + 2 ^ p) := by rw [Nat.or_two_pow_eq_add_of_lt hr]
    _ = 2 ^ (p + 1) * q + (r + 2 ^ p) := (Nat.two_pow_add_eq_or_of_lt hlt1 q).symm
    _ = (2 ^ (p + 1) * q + r) + 2 ^ p := by omega

@[expose] def lorS (d : Nat → Bool) (g : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => if d i = true then acc else Nat.lor acc (Nat.shiftLeft 1 (g i))) n

@[expose] def addS (d : Nat → Bool) (g : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => if d i = true then acc else Nat.add acc (Nat.shiftLeft 1 (g i))) n

theorem lorS_le_addS (d : Nat → Bool) (g : Nat → Nat) (n : Nat) :
    lorS d g n ≤ addS d g n ∧ (lorS d g n = addS d g n →
      ∀ i < n, ∀ i' < n, d i = false → d i' = false → g i = g i' → i = i') := by
  induction n with
  | zero => exact ⟨Nat.le_refl _, fun _ i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hl : lorS d g (n + 1) = if d n = true then lorS d g n
        else lorS d g n ||| 2 ^ g n := by
      show (if d n = true then lorS d g n else Nat.lor (lorS d g n) (Nat.shiftLeft 1 (g n))) = _
      rw [show Nat.shiftLeft 1 (g n) = 2 ^ g n from Nat.one_shiftLeft _]
      rfl
    have ha : addS d g (n + 1) = if d n = true then addS d g n else addS d g n + 2 ^ g n := by
      show (if d n = true then addS d g n else Nat.add (addS d g n) (Nat.shiftLeft 1 (g n))) = _
      rw [show Nat.shiftLeft 1 (g n) = 2 ^ g n from Nat.one_shiftLeft _]
      rfl
    by_cases hd : d n = true
    · rw [hl, ha, if_pos hd, if_pos hd]
      refine ⟨ih1, fun heq i hi i' hi' hdi hdi' hg => ih2 heq i ?_ i' ?_ hdi hdi' hg⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
        · exact h
        · rw [hd] at hdi
          exact absurd hdi (by simp)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | rfl
        · exact h
        · rw [hd] at hdi'
          exact absurd hdi' (by simp)
    · have hd' : d n = false := by simpa using hd
      rw [hl, ha, if_neg hd, if_neg hd]
      have hpos : 0 < 2 ^ g n := Nat.two_pow_pos _
      cases hb : (lorS d g n).testBit (g n)
      · rw [or_two_pow_of_testBit_false hb]
        refine ⟨by omega, fun heq i hi i' hi' hdi hdi' hg => ?_⟩
        have heq' : lorS d g n = addS d g n := by omega
        have hdist := ih2 heq'
        have hmem : ∀ k < n, d k = false → (lorS d g n).testBit (g k) = true := fun k hk hdk =>
          (testBit_fold_or_skip d g n (g k)).2 ⟨k, hk, hdk, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h' | rfl
        · exact hdist i h i' h' hdi hdi' hg
        · exfalso
          have := hmem i h hdi
          rw [hg, hb] at this
          exact absurd this (by simp)
        · exfalso
          have := hmem i' h' hdi'
          rw [← hg, hb] at this
          exact absurd this (by simp)
        · rfl
      · rw [or_two_pow_of_testBit_true hb]
        refine ⟨by omega, fun heq => ?_⟩
        omega

theorem land_shiftRight_one_eq (S i : Nat) :
    Nat.land (Nat.shiftRight S i) 1 = if S.testBit i = true then 1 else 0 := by
  have e : Nat.land (Nat.shiftRight S i) 1 = S / 2 ^ i % 2 := by
    rw [show Nat.land (Nat.shiftRight S i) 1 = (S >>> i) &&& 1 from rfl, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  have : S / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases h : S / 2 ^ i % 2 = 1
  · simp [h]
  · have h0 : S / 2 ^ i % 2 = 0 := by omega
    simp [h0]

@[expose] def cnt (f : Nat → Bool) (n : Nat) : Nat := ((List.range n).filter f).length

theorem cnt_succ (f : Nat → Bool) (n : Nat) :
    cnt f (n + 1) = cnt f n + if f n = true then 1 else 0 := by
  unfold cnt
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : f n = true <;> simp [h]

theorem cnt_congr {f g : Nat → Bool} {n : Nat} (h : ∀ p < n, f p = g p) : cnt f n = cnt g n := by
  unfold cnt
  rw [List.filter_congr (fun p hp => h p (List.mem_range.1 hp))]

theorem rec_pop (S n : Nat) : (Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) n) =
      cnt (fun i => S.testBit i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.add (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.add acc (Nat.land (Nat.shiftRight S i) 1)) n)
        (Nat.land (Nat.shiftRight S n) 1) = _
    rw [ih, land_shiftRight_one_eq, cnt_succ]
    rfl

theorem popK_eq (S : Nat) : popK S = cnt (fun i => S.testBit i) 693 := by
  unfold popK
  rw [letN_eq]
  exact rec_pop S 693

theorem rec_congr {f g : Nat → Nat → Nat} (h : ∀ i acc, f i acc = g i acc) (n : Nat) :
    Nat.rec (motive := fun _ => Nat) 0 f n = Nat.rec (motive := fun _ => Nat) 0 g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show f n (Nat.rec (motive := fun _ => Nat) 0 f n) = g n (Nat.rec (motive := fun _ => Nat) 0 g n)
    rw [h, ih]

theorem imgP_aux (T M n : Nat) : Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 10 T (at' 10 M i)))) n =
      lorS (fun _ => false) (fun i => fd 10 T (fd 10 M i)) n := by
  unfold lorS
  refine rec_congr (fun i acc => ?_) n
  simp only [at'_eq, Bool.false_eq_true, ↓reduceIte]

theorem imgP_eq (T M : Nat) :
    imgP T M = lorS (fun _ => false) (fun i => fd 10 T (fd 10 M i)) 126 := by
  unfold imgP
  exact imgP_aux T M 126

theorem testBit_imgP (T M q : Nat) :
    (imgP T M).testBit q = true ↔ ∃ i < 126, fd 10 T (fd 10 M i) = q := by
  rw [imgP_eq, lorS, testBit_fold_or_skip]
  simp

theorem listsP_aux (M n : Nat) : Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 10 M i))) n =
      lorS (fun _ => false) (fun i => fd 10 M i) n := by
  unfold lorS
  refine rec_congr (fun i acc => ?_) n
  simp only [at'_eq, Bool.false_eq_true, ↓reduceIte]

theorem listsP_spec {S M : Nat} (h : listsP S M = true) :
    S < 2 ^ 693 ∧ ∀ p, S.testBit p = true ↔ ∃ i < 126, fd 10 M i = p := by
  unfold listsP at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h1, -, h3, -, -⟩ := h
  have e : (Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (at' 10 M i))) 126) =
        lorS (fun _ => false) (fun i => fd 10 M i) 126 :=
    listsP_aux M 126
  rw [e] at h3
  refine ⟨by rw [← Nat.one_shiftLeft]; exact h1, fun p => ?_⟩
  rw [← h3, lorS, testBit_fold_or_skip]
  simp

theorem prodK_eq (c : Nat) : prodK c = prodCoordC c := by
  have h1 : ∀ y < 4, f4mul 1 y = y := by decide
  have h2 := h1 (coord c 0) (by unfold coord; omega)
  unfold prodK prodCoordC
  show f4K (f4K (f4K (f4K (f4K (f4K 1 (crdK c 0)) (crdK c 1)) (crdK c 2)) (crdK c 3)) (crdK c 4))
    (crdK c 5) = _
  simp only [f4K_eq, crdK_eq, h2]

theorem nzK_eq (c : Nat) : nzK c = nzC c := by
  unfold nzK
  rw [weightK_eq]
  unfold weightC nzC
  simp only [List.range_succ, List.range_zero, List.nil_append, List.filter_cons, List.filter_nil]
  by_cases h0 : coord c 0 = 0 <;> by_cases h1 : coord c 1 = 0 <;> by_cases h2 : coord c 2 = 0 <;>
    by_cases h3 : coord c 3 = 0 <;> by_cases h4 : coord c 4 = 0 <;> by_cases h5 : coord c 5 = 0 <;>
    simp [h0, h1, h2, h3, h4, h5]

theorem testBit_rootK (UP c p : Nat) :
    (rootK UP c).testBit p = true ↔ p < 693 ∧ (nzK (fd 12 UP p) = 2 ∨
      (nzK (fd 12 UP p) = 6 ∧ prodK (fd 12 UP p) = c)) := by
  have e : rootK UP c = Nat.rec (motive := fun _ => Nat) 0
      (fun i acc => if ((nzK (fd 12 UP i)).beq 2 || ((nzK (fd 12 UP i)).beq 6 &&
        (prodK (fd 12 UP i)).beq c)) = true then Nat.lor acc (Nat.shiftLeft 1 i) else acc) 693 := by
    unfold rootK
    simp only [letN_eq, nIf_eq, orB_eq, andB_eq, at'_eq]
  rw [e, testBit_fold_or]
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq]
  constructor
  · rintro ⟨i, hi, h1, rfl⟩
    exact ⟨hi, h1⟩
  · rintro ⟨hp, h⟩
    exact ⟨p, hp, h, rfl⟩

theorem lt_of_testBit {S : Nat} (hS : S < 2 ^ 693) {p : Nat} (h : S.testBit p = true) :
    p < 693 := by
  by_contra hp
  have := Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hS (Nat.pow_le_pow_right (by norm_num)
    (Nat.not_lt.1 hp)))
  rw [this] at h
  exact absurd h (by simp)

@[expose] def fl (S : Nat) : Flags := Array.ofFn (n := 693) fun p => S.testBit p

theorem fl_size (S : Nat) : (fl S).size = 693 := by simp [fl]

theorem fl_get (S : Nat) {p : Nat} (hp : p < 693) : (fl S)[p]! = S.testBit p := by
  unfold fl
  rw [getElem!_pos _ _ (by simpa using hp), Array.getElem_ofFn]

theorem ofFn_congr' {α : Type} {n : Nat} {f g : Fin n → α} (h : ∀ i, f i = g i) :
    Array.ofFn f = Array.ofFn g := by
  have : f = g := funext h
  rw [this]

theorem flags_eq {F : Flags} {S : Nat} (hs : F.size = 693) (h : ∀ p < 693, F[p]! = S.testBit p) :
    F = fl S := by
  have e : F = Array.ofFn (n := 693) (fun p : Fin 693 => F[p.val]!) := by
    apply Array.ext
    · simp [hs]
    · intro i h1 h2
      rw [Array.getElem_ofFn]
      exact (getElem!_pos F i h1).symm
  rw [e]
  exact ofFn_congr' (fun p => h p p.isLt)

theorem push_getElem!_lt {α : Type} [Inhabited α] (a : Array α) (x : α) {i : Nat}
    (hi : i < a.size) : (a.push x)[i]! = a[i]! := by
  simp [getElem!_def, Array.getElem?_push, hi, Nat.ne_of_lt hi, Array.getElem?_eq_getElem hi]

theorem push_getElem!_size {α : Type} [Inhabited α] (a : Array α) (x : α) :
    (a.push x)[a.size]! = x := by
  simp [getElem!_def, Array.getElem?_push]

theorem filterRange_eq (p : Nat → Bool) (n : Nat) (acc : List Nat) :
    filterRange p n acc = (List.range n).filter p ++ acc := by
  induction n generalizing acc with
  | zero => simp [filterRange]
  | succ n ih =>
    rw [filterRange, ih, List.range_succ, List.filter_append]
    by_cases h : p n = true <;> simp [h]

theorem members_eq (F : Flags) : members F = (List.range 693).filter (fun p => F[p]!) := by
  unfold members
  rw [filterRange_eq, List.append_nil]

theorem mem_members {F : Flags} {p : Nat} : p ∈ members F ↔ p < 693 ∧ F[p]! = true := by
  rw [members_eq]
  simp

theorem mem_members_fl {S p : Nat} : p ∈ members (fl S) ↔ p < 693 ∧ S.testBit p = true := by
  rw [mem_members]
  constructor
  · rintro ⟨h1, h2⟩
    rw [fl_get S h1] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [fl_get S h1]
    exact ⟨h1, h2⟩

theorem len_filter_members (S : Nat) (g : Nat → Bool) :
    ((members (fl S)).filter g).length = cnt (fun p => S.testBit p && g p) 693 := by
  rw [members_eq, List.filter_filter]
  unfold cnt
  rw [List.filter_congr (fun p hp => ?_)]
  rw [fl_get S (List.mem_range.1 hp)]
  exact Bool.and_comm _ _

@[expose] def bitW (a : Array UInt64) (q : Nat) : Bool := (a[q / 64]!).toNat.testBit (q % 64)

theorem toNat_or_shl (w : UInt64) {k : Nat} (hk : k < 64) :
    (w ||| ((1 : UInt64) <<< k.toUInt64)).toNat = w.toNat ||| 2 ^ k := by
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft]
  have h1 : (k.toUInt64).toNat = k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.mod_eq_of_lt hk]
  have h2 : (1 : UInt64).toNat = 1 := rfl
  rw [h2, Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hk)]

theorem bitW_setBitW (a : Array UInt64) (ha : a.size = 11) {p q : Nat} (hp : p < 704)
    (hq : q < 704) : bitW (setBitW a p) q = (bitW a q || decide (q = p)) := by
  have hsz : (setBitW a p).size = 11 := by simp [setBitW, ha]
  have hq64 : q / 64 < 11 := by omega
  have hp64 : p / 64 < 11 := by omega
  unfold bitW
  rw [getElem!_pos _ _ (by rw [hsz]; exact hq64), getElem!_pos _ _ (by rw [ha]; exact hq64)]
  unfold setBitW
  rw [Array.getElem_modify]
  by_cases hpq : p / 64 = q / 64
  · rw [if_pos hpq, toNat_or_shl _ (Nat.mod_lt _ (by norm_num)), Nat.testBit_or,
      Nat.testBit_two_pow]
    have : (decide (p % 64 = q % 64)) = (decide (q = p)) := by
      apply decide_eq_decide.2
      constructor
      · intro h; omega
      · intro h; subst h; rfl
    rw [this]
  · rw [if_neg hpq]
    have : decide (q = p) = false := by
      simp only [decide_eq_false_iff_not]
      intro h; subst h; exact hpq rfl
    rw [this, Bool.or_false]

theorem foldl_setBitW_size (L : List Nat) (a : Array UInt64) (ha : a.size = 11) :
    (L.foldl setBitW a).size = 11 := by
  induction L generalizing a with
  | nil => exact ha
  | cons p t ih =>
    rw [List.foldl_cons]
    exact ih _ (by simp [setBitW, ha])

theorem bitW_foldl (L : List Nat) (hL : ∀ p ∈ L, p < 704) (a : Array UInt64) (ha : a.size = 11)
    {q : Nat} (hq : q < 704) : bitW (L.foldl setBitW a) q = (bitW a q || decide (q ∈ L)) := by
  induction L generalizing a with
  | nil => simp
  | cons p t ih =>
    rw [List.foldl_cons,
      ih (fun x hx => hL x (List.mem_cons_of_mem _ hx)) _ (by simp [setBitW, ha]),
      bitW_setBitW a ha (hL p List.mem_cons_self) hq]
    by_cases h1 : q = p
    · simp [h1]
    · by_cases h2 : q ∈ t <;> simp [h1, h2, Bool.or_assoc]

theorem bitW_replicate_zero (q : Nat) : bitW (Array.replicate 11 0) q = false := by
  unfold bitW
  have : (Array.replicate 11 (0 : UInt64))[q / 64]! = 0 := by
    by_cases h : q / 64 < 11
    · rw [getElem!_pos _ _ (by simpa using h)]
      simp
    · rw [getElem!_neg _ _ (by simpa using h)]
      rfl
  rw [this]
  simp

theorem packList_size (L : List Nat) : (packList L).size = 11 :=
  foldl_setBitW_size L _ (by simp)

theorem bitW_packList {L : List Nat} (hL : ∀ p ∈ L, p < 704) {q : Nat} (hq : q < 704) :
    bitW (packList L) q = decide (q ∈ L) := by
  unfold packList
  rw [bitW_foldl L hL _ (by simp) hq, bitW_replicate_zero]
  simp

theorem packList_eq_iff {L L' : List Nat} (hL : ∀ p ∈ L, p < 704) (hL' : ∀ p ∈ L', p < 704) :
    packList L = packList L' ↔ ∀ q, q ∈ L ↔ q ∈ L' := by
  constructor
  · intro h q
    by_cases hq : q < 704
    · have := bitW_packList hL hq
      rw [h, bitW_packList hL' hq] at this
      simpa using this.symm
    · constructor
      · intro hm; exact absurd (hL q hm) hq
      · intro hm; exact absurd (hL' q hm) hq
  · intro h
    apply Array.ext
    · rw [packList_size, packList_size]
    · intro i hi1 hi2
      have hi : i < 11 := by rw [packList_size] at hi1; exact hi1
      have e : ∀ j < 64, ((packList L)[i]).toNat.testBit j =
          ((packList L')[i]).toNat.testBit j := by
        intro j hj
        have hq : 64 * i + j < 704 := by omega
        have h1 := bitW_packList hL hq
        have h2 := bitW_packList hL' hq
        have e1 : (64 * i + j) / 64 = i := by omega
        have e2 : (64 * i + j) % 64 = j := by omega
        unfold bitW at h1 h2
        rw [e1, e2, getElem!_pos _ _ (by rw [packList_size]; exact hi)] at h1 h2
        rw [h1, h2]
        exact decide_eq_decide.2 (h _)
      apply UInt64.toNat_inj.1
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < 64
      · exact e j hj
      · have hlt1 := UInt64.toNat_lt (packList L)[i]
        have hlt2 := UInt64.toNat_lt (packList L')[i]
        rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hlt1
            (Nat.pow_le_pow_right (by norm_num) (by omega))),
          Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hlt2
            (Nat.pow_le_pow_right (by norm_num) (by omega)))]

@[expose] def famFold (H : Array Flags) (m : Nat) : Std.HashMap (Array UInt64) Nat :=
  (List.range m).foldl (fun mp k => mp.insert (packList (members H[k]!)) k) ∅

theorem famFold_succ (H : Array Flags) (m : Nat) :
    famFold H (m + 1) = (famFold H m).insert (packList (members H[m]!)) m := by
  unfold famFold
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem famFold_getD (H : Array Flags) (n : Nat) :
    ∀ m, (∀ j < m, ∀ j' < m, packList (members H[j]!) = packList (members H[j']!) → j = j') →
      ∀ j < m, (famFold H m).getD (packList (members H[j]!)) n = j
  | 0, _ => fun j hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, hinj => by
    have ih := famFold_getD H n m (fun j hj j' hj' h => hinj j (by omega) j' (by omega) h)
    rw [famFold_succ]
    intro j hj
    rw [Std.HashMap.getD_insert]
    by_cases hjm : j = m
    · subst hjm
      simp
    · have hne : packList (members H[m]!) ≠ packList (members H[j]!) := fun h =>
        hjm (hinj j (by omega) m (by omega) h.symm)
      have : ¬ (packList (members H[m]!) == packList (members H[j]!)) = true := by
        simpa using hne
      rw [if_neg this]
      exact ih j (by omega)

theorem famIndex_eq (H : Array Flags) : famIndex H = famFold H H.size := rfl

end CFSG.KC.Misc.Xi

end
