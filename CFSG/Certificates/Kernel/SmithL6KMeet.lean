module

public import CFSG.Certificates.Kernel.SmithL6KSound
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.Kernel
open Finset

@[expose] def setM (M : Nat) : Finset Nat := (range 64).filter fun x => M.testBit x = true

@[expose] def annS (A : Finset Nat) : Finset Nat :=
  (range 64).filter fun φ => ∀ x ∈ A, form φ x = false

@[expose] def XorClosed (A : Finset Nat) : Prop :=
  A ⊆ range 64 ∧ 0 ∈ A ∧ ∀ x ∈ A, ∀ y ∈ A, x ^^^ y ∈ A

@[expose] def chi (φ x : Nat) : ℤ := if form φ x then -1 else 1

theorem mem_annS {A : Finset Nat} {φ : Nat} :
    φ ∈ annS A ↔ φ < 64 ∧ ∀ x ∈ A, form φ x = false := by
  unfold annS
  rw [Finset.mem_filter, Finset.mem_range]

theorem chi_xor (φ x y : Nat) : chi φ (x ^^^ y) = chi φ x * chi φ y := by
  unfold chi
  rw [form_xor_right]
  cases form φ x <;> cases form φ y <;> simp

theorem form_zero (φ : Nat) : form φ 0 = false := by
  unfold form
  rw [Nat.and_zero]
  rfl

theorem form_two_pow {b : Nat} (hb : b < 6) (x : Nat) : form (2 ^ b) x = x.testBit b := by
  unfold form par
  have e : ∀ t, (2 ^ b &&& x).testBit t = (decide (b = t) && x.testBit t) := fun t => by
    rw [Nat.testBit_and, Nat.testBit_two_pow]
  simp only [e]
  match b, hb with
  | 0, _ => simp [List.range_succ]
  | 1, _ => simp [List.range_succ]
  | 2, _ => simp [List.range_succ]
  | 3, _ => simp [List.range_succ]
  | 4, _ => simp [List.range_succ]
  | 5, _ => simp [List.range_succ]

theorem exists_bit : ∀ x < 64, x ≠ 0 → ∃ b < 6, x.testBit b = true := by decide

theorem sum_flip {s : Finset Nat} {f : Nat → ℤ} (σ : Nat → Nat) (hσ : ∀ a ∈ s, σ a ∈ s)
    (hinv : ∀ a ∈ s, σ (σ a) = a) (hf : ∀ a ∈ s, f (σ a) = -f a) : ∑ a ∈ s, f a = 0 := by
  have h : ∑ a ∈ s, f a = ∑ a ∈ s, -f a :=
    Finset.sum_nbij' σ σ hσ hσ hinv hinv fun a ha => by rw [hf a ha, neg_neg]
  rw [Finset.sum_neg_distrib] at h
  linarith

theorem sum_chi_forms {x : Nat} (hx : x < 64) :
    ∑ φ ∈ range 64, chi φ x = if x = 0 then 64 else 0 := by
  by_cases h0 : x = 0
  · subst h0
    simp [chi, form_zero]
  · rw [if_neg h0]
    obtain ⟨b, hb, hxb⟩ := exists_bit x hx h0
    have hb64 : 2 ^ b < 64 := Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by omega) hb) (by omega)
    refine sum_flip (fun φ => φ ^^^ 2 ^ b) (fun φ hφ => ?_) (fun φ _ => ?_) (fun φ _ => ?_)
    · rw [Finset.mem_range] at hφ ⊢
      exact xor_lt64 hφ hb64
    · simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · unfold chi
      rw [form_xor_left, form_two_pow hb, hxb]
      cases form φ x <;> simp

theorem sum_chi_vecs {A : Finset Nat} (hA : XorClosed A) {φ : Nat} (hφ : φ < 64) :
    ∑ x ∈ A, chi φ x = if φ ∈ annS A then (A.card : ℤ) else 0 := by
  by_cases h : ∀ x ∈ A, form φ x = false
  · rw [if_pos (mem_annS.mpr ⟨hφ, h⟩)]
    rw [Finset.sum_congr rfl fun x hx => (by unfold chi; rw [h x hx]; rfl : chi φ x = 1)]
    simp
  · rw [if_neg fun hm => h (mem_annS.mp hm).2]
    have h' : ∃ x0 ∈ A, form φ x0 = true := by
      by_cases hc : ∃ x0 ∈ A, form φ x0 = true
      · exact hc
      · exact absurd (fun x hx => by
          cases hfx : form φ x
          · rfl
          · exact absurd ⟨x, hx, hfx⟩ hc) h
    obtain ⟨x0, hx0, hf0⟩ := h'
    refine sum_flip (fun x => x ^^^ x0) (fun x hx => hA.2.2 x hx x0 hx0) (fun x _ => ?_)
      (fun x _ => ?_)
    · simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · rw [chi_xor]
      unfold chi
      rw [hf0]
      cases form φ x <;> simp

theorem annS_sub (A : Finset Nat) : annS A ⊆ range 64 := Finset.filter_subset _ _

theorem card_mul_annInter {A B : Finset Nat} (hA : XorClosed A) (hB : XorClosed B) :
    (A.card * B.card * (annS A ∩ annS B).card : ℤ) = 64 * (A ∩ B).card := by
  have h1 : ∑ φ ∈ range 64, (∑ a ∈ A, chi φ a) * (∑ b ∈ B, chi φ b) =
      (A.card * B.card * (annS A ∩ annS B).card : ℤ) := by
    rw [Finset.sum_congr rfl fun φ hφ => by
      rw [sum_chi_vecs hA (Finset.mem_range.mp hφ), sum_chi_vecs hB (Finset.mem_range.mp hφ)]]
    have e : ∀ φ ∈ range 64, ((if φ ∈ annS A then (A.card : ℤ) else 0) *
        (if φ ∈ annS B then (B.card : ℤ) else 0)) =
        if φ ∈ annS A ∩ annS B then (A.card * B.card : ℤ) else 0 := fun φ _ => by
      by_cases ha : φ ∈ annS A <;> by_cases hb : φ ∈ annS B <;> simp [ha, hb]
    rw [Finset.sum_congr rfl e, Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans (annS_sub A)), Finset.sum_const,
      nsmul_eq_mul]
    ring
  have h2 : ∑ φ ∈ range 64, (∑ a ∈ A, chi φ a) * (∑ b ∈ B, chi φ b) = 64 * (A ∩ B).card := by
    simp_rw [Finset.sum_mul_sum, ← chi_xor]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
    have e : ∀ a ∈ A, ∀ b ∈ B, ∑ φ ∈ range 64, chi φ (a ^^^ b) = if a = b then 64 else 0 :=
      fun a ha b hb => by
        rw [sum_chi_forms (xor_lt64 (Finset.mem_range.mp (hA.1 ha))
          (Finset.mem_range.mp (hB.1 hb)))]
        by_cases hab : a = b
        · subst hab
          simp
        · rw [if_neg hab, if_neg fun h => hab (eq_of_xor_eq_zero h)]
    rw [Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => e a ha b hb]
    simp_rw [Finset.sum_ite_eq]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_mem_eq_inter]
    ring
  rw [← h1, h2]

theorem card_annInter {A B : Finset Nat} (hA : XorClosed A) (hB : XorClosed B) (hcA : A.card = 8)
    (hcB : B.card = 8) : (annS A ∩ annS B).card = (A ∩ B).card := by
  have h := card_mul_annInter hA hB
  rw [hcA, hcB] at h
  push_cast at h
  have h' : ((annS A ∩ annS B).card : ℤ) = (A ∩ B).card := by linarith
  exact_mod_cast h'

theorem foldl_or_testBit (g : Nat → Nat) (c : Nat → Bool) (l : List Nat) (S x : Nat) :
    (l.foldl (fun acc d => if c d then acc ||| 2 ^ g d else acc) S).testBit x =
      (S.testBit x || l.any fun d => c d && g d == x) := by
  induction l generalizing S with
  | nil => simp
  | cons d l ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    cases hc : c d
    · simp
    · rw [if_pos rfl, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases h : g d = x
      · simp [h]
      · have h' : (g d == x) = false := by simp [h]
        simp [h, h']

@[expose] def comb (a b c d : Nat) : Nat :=
  (if d.testBit 0 then a else 0) ^^^ (if d.testBit 1 then b else 0) ^^^ (if d.testBit 2 then c else 0)

theorem spanMask_testBit (a b c x : Nat) :
    (spanMask a b c).testBit x = (List.range 8).any fun d => comb a b c d == x := by
  unfold spanMask
  have e := foldl_or_testBit (comb a b c) (fun _ => true) (List.range 8) 0 x
  simp only [if_true, Bool.true_and, Nat.zero_testBit, Bool.false_or] at e
  exact e

theorem mem_setM {M x : Nat} : x ∈ setM M ↔ x < 64 ∧ M.testBit x = true := by
  unfold setM
  rw [Finset.mem_filter, Finset.mem_range]

theorem ite_xor (p : Bool) (a b : Nat) :
    ((if p then a else 0) ^^^ (if p then b else 0)) = if p then a ^^^ b else 0 := by
  cases p <;> simp

theorem comb_xor (a b c d d' : Nat) : comb a b c d ^^^ comb a b c d' = comb a b c (d ^^^ d') := by
  unfold comb
  simp only [Nat.testBit_xor]
  have key : ∀ (p q : Bool) (u : Nat), ((if p then u else 0) ^^^ (if q then u else 0)) =
      if (p ^^ q) then u else 0 := fun p q u => by cases p <;> cases q <;> simp
  rw [← key (d.testBit 0), ← key (d.testBit 1), ← key (d.testBit 2)]
  generalize (if d.testBit 0 = true then a else 0) = A
  generalize (if d.testBit 1 = true then b else 0) = B
  generalize (if d.testBit 2 = true then c else 0) = C
  generalize (if d'.testBit 0 = true then a else 0) = A'
  generalize (if d'.testBit 1 = true then b else 0) = B'
  generalize (if d'.testBit 2 = true then c else 0) = C'
  apply Nat.eq_of_testBit_eq
  intro t
  simp only [Nat.testBit_xor]
  cases A.testBit t <;> cases B.testBit t <;> cases C.testBit t <;> cases A'.testBit t <;>
    cases B'.testBit t <;> cases C'.testBit t <;> rfl

theorem comb_one (a b c : Nat) : comb a b c 1 = a := by
  have e0 : (1 : Nat).testBit 0 = true := by decide
  have e1 : (1 : Nat).testBit 1 = false := by decide
  have e2 : (1 : Nat).testBit 2 = false := by decide
  simp [comb, e0, e1, e2]

theorem comb_two (a b c : Nat) : comb a b c 2 = b := by
  have e0 : (2 : Nat).testBit 0 = false := by decide
  have e1 : (2 : Nat).testBit 1 = true := by decide
  have e2 : (2 : Nat).testBit 2 = false := by decide
  simp [comb, e0, e1, e2]

theorem comb_four (a b c : Nat) : comb a b c 4 = c := by
  have e0 : (4 : Nat).testBit 0 = false := by decide
  have e1 : (4 : Nat).testBit 1 = false := by decide
  have e2 : (4 : Nat).testBit 2 = true := by decide
  simp [comb, e0, e1, e2]

theorem comb_lt {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) (d : Nat) :
    comb a b c d < 64 := by
  unfold comb
  refine xor_lt64 (xor_lt64 ?_ ?_) ?_ <;> split <;> omega

theorem mem_span {a b c x : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    x ∈ setM (spanMask a b c) ↔ ∃ d < 8, comb a b c d = x := by
  rw [mem_setM, spanMask_testBit, List.any_eq_true]
  constructor
  · rintro ⟨-, d, hd, he⟩
    exact ⟨d, List.mem_range.mp hd, beq_iff_eq.mp he⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨comb_lt ha hb hc d, d, List.mem_range.mpr hd, beq_self_eq_true _⟩

theorem xorClosed_span {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    XorClosed (setM (spanMask a b c)) := by
  refine ⟨fun x hx => Finset.mem_range.mpr (mem_setM.mp hx).1, ?_, ?_⟩
  · rw [mem_span ha hb hc]
    exact ⟨0, by omega, by simp [comb]⟩
  · intro x hx y hy
    rw [mem_span ha hb hc] at hx hy ⊢
    obtain ⟨d, hd, rfl⟩ := hx
    obtain ⟨d', hd', rfl⟩ := hy
    exact ⟨d ^^^ d', Nat.xor_lt_two_pow (n := 3) hd hd', (comb_xor a b c d d').symm⟩

theorem form_comb (φ a b c d : Nat) : form φ (comb a b c d) =
    ((d.testBit 0 && form φ a) ^^ (d.testBit 1 && form φ b) ^^ (d.testBit 2 && form φ c)) := by
  unfold comb
  rw [form_xor_right, form_xor_right]
  cases d.testBit 0 <;> cases d.testBit 1 <;> cases d.testBit 2 <;> simp [form_zero]

theorem annMaskOf_testBit (a b c φ : Nat) : (annMaskOf a b c).testBit φ =
    (decide (φ < 64) && !form φ a && !form φ b && !form φ c) := by
  unfold annMaskOf
  have e := foldl_or_testBit (fun ψ => ψ) (fun ψ => !form ψ a && !form ψ b && !form ψ c)
    (List.range 64) 0 φ
  simp only [Nat.zero_testBit, Bool.false_or] at e
  rw [e]
  by_cases h : φ < 64
  · have e2 : ((List.range 64).any fun d => (!form d a && !form d b && !form d c) && d == φ) =
        (!form φ a && !form φ b && !form φ c) := by
      cases hq : (!form φ a && !form φ b && !form φ c)
      · rw [Bool.eq_false_iff]
        intro hany
        rw [List.any_eq_true] at hany
        obtain ⟨d, -, hd⟩ := hany
        rw [Bool.and_eq_true, beq_iff_eq] at hd
        rw [← hd.2, hd.1] at hq
        exact Bool.false_ne_true hq.symm
      · rw [List.any_eq_true]
        exact ⟨φ, List.mem_range.mpr h, by rw [hq, beq_self_eq_true]; rfl⟩
    rw [e2, decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and, Bool.false_and, Bool.false_and, Bool.eq_false_iff]
    intro hany
    rw [List.any_eq_true] at hany
    obtain ⟨d, hd, hdd⟩ := hany
    rw [Bool.and_eq_true, beq_iff_eq] at hdd
    exact h (hdd.2 ▸ List.mem_range.mp hd)

theorem annS_span {a b c : Nat} (ha : a < 64) (hb : b < 64) (hc : c < 64) :
    annS (setM (spanMask a b c)) = setM (annMaskOf a b c) := by
  ext φ
  rw [mem_setM, annMaskOf_testBit]
  unfold annS
  rw [Finset.mem_filter, Finset.mem_range]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨hφ, h⟩
    have hx : ∀ d < 8, form φ (comb a b c d) = false := fun d hd =>
      h _ ((mem_span ha hb hc).mpr ⟨d, hd, rfl⟩)
    have h1 := hx 1 (by omega)
    have h2 := hx 2 (by omega)
    have h4 := hx 4 (by omega)
    rw [comb_one] at h1
    rw [comb_two] at h2
    rw [comb_four] at h4
    exact ⟨hφ, ⟨⟨hφ, h1⟩, h2⟩, h4⟩
  · rintro ⟨hφ, ⟨⟨-, h1⟩, h2⟩, h4⟩
    refine ⟨hφ, fun x hx => ?_⟩
    obtain ⟨d, -, rfl⟩ := (mem_span ha hb hc).mp hx
    rw [form_comb, h1, h2, h4]
    simp

theorem setM_and (M N : Nat) : setM (M &&& N) = setM M ∩ setM N := by
  ext x
  rw [Finset.mem_inter, mem_setM, mem_setM, mem_setM, Nat.testBit_and, Bool.and_eq_true]
  tauto

theorem card_filter_range (p : Nat → Bool) (n : Nat) :
    ((range n).filter fun x => p x = true).card = (List.range n).countP p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append, ← ih]
    by_cases h : p n = true
    · rw [if_pos h, Finset.card_insert_of_notMem (fun hm => by
        simp at hm)]
      simp [h]
    · rw [if_neg h]
      simp [h]

theorem getD_map_false {α : Type} (o : Option α) (P : α → Bool) :
    (o.map P).getD false = o.any P := by
  cases o <;> rfl

theorem countMN_eq {M N : Nat} (horth : ∀ v < 64, ∀ φ < 64, M.testBit v = true →
    N.testBit φ = true → form φ v = false) (hM : M.testBit 0 = true) (hN : N.testBit 0 = true) :
    countMN M N = ((setM M).card - 1) * ((setM N).card - 1) := by
  unfold countMN
  rw [tvList_toList, List.countP_filterMap, ← card_filter_range]
  have e : ((range 4096).filter fun n => ((if n / 64 ≠ 0 ∧ n % 64 ≠ 0 ∧ form (n % 64) (n / 64) = false
      then some (n / 64, n % 64) else none).any fun p : Nat × Nat =>
        M.testBit p.1 && N.testBit p.2) = true).card =
      (((setM M).erase 0) ×ˢ ((setM N).erase 0)).card := by
    refine Finset.card_nbij' (fun n => (n / 64, n % 64)) (fun p => 64 * p.1 + p.2) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hn
      obtain ⟨hn, hq⟩ := hn
      split at hq
      · rename_i hc
        simp only [Option.any_some, Bool.and_eq_true] at hq
        simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase, mem_setM]
        exact ⟨⟨hc.1, by omega, hq.1⟩, ⟨hc.2.1, by omega, hq.2⟩⟩
      · simp at hq
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
        mem_setM] at hp
      obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩ := hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      have d1 : (64 * p.1 + p.2) / 64 = p.1 := by omega
      have d2 : (64 * p.1 + p.2) % 64 = p.2 := by omega
      rw [d1, d2, if_pos ⟨h1, h4, horth _ h2 _ h5 h3 h6⟩]
      exact ⟨by omega, by simp [h3, h6]⟩
    · intro n _
      simp only
      omega
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
        mem_setM] at hp
      have : p.2 < 64 := hp.2.2.1
      ext <;> simp only <;> omega
  simp only [getD_map_false]
  rw [e, Finset.card_product, Finset.card_erase_of_mem (mem_setM.mpr ⟨by omega, hM⟩),
    Finset.card_erase_of_mem (mem_setM.mpr ⟨by omega, hN⟩)]

theorem xorClosed_inter {A B : Finset Nat} (hA : XorClosed A) (hB : XorClosed B) :
    XorClosed (A ∩ B) := by
  refine ⟨Finset.inter_subset_left.trans hA.1, Finset.mem_inter.mpr ⟨hA.2.1, hB.2.1⟩, ?_⟩
  intro x hx y hy
  rw [Finset.mem_inter] at hx hy ⊢
  exact ⟨hA.2.2 x hx.1 y hy.1, hB.2.2 x hx.2 y hy.2⟩

theorem divisors_le8 : ∀ x ≤ 8, 0 < x → x ∣ 64 → x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 8 := by decide

theorem card_pow2 {X : Finset Nat} (hX : XorClosed X) (h8 : X.card ≤ 8) :
    X.card = 1 ∨ X.card = 2 ∨ X.card = 4 ∨ X.card = 8 := by
  have h := card_mul_annInter hX hX
  rw [Finset.inter_self, Finset.inter_self] at h
  have h' : X.card * (X.card * (annS X).card) = X.card * 64 := by
    have : (X.card * (X.card * (annS X).card) : ℤ) = X.card * 64 := by linarith
    exact_mod_cast this
  have hpos : 0 < X.card := Finset.card_pos.mpr ⟨0, hX.2.1⟩
  have e := Nat.eq_of_mul_eq_mul_left hpos h'
  exact divisors_le8 _ h8 hpos (Dvd.intro _ e)

theorem xorClosed_wMask {i : Nat} (hi : wData[i]! < 262144) : XorClosed (setM (wMask i)) :=
  xorClosed_span (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by omega)

theorem meetCardK_formula {i j : Nat} (hi : wData[i]! < 262144) (hj : wData[j]! < 262144)
    (hci : (setM (wMask i)).card = 8) (hcj : (setM (wMask j)).card = 8) :
    meetCardK i j = ((setM (wMask i &&& wMask j)).card - 1) ^ 2 := by
  have b1 : ∀ c : Nat, c < 262144 → c % 64 < 64 ∧ c / 64 % 64 < 64 ∧ c / 4096 < 64 := fun c hc =>
    ⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega), by omega⟩
  obtain ⟨ai, bi, ci⟩ := b1 _ hi
  obtain ⟨aj, bj, cj⟩ := b1 _ hj
  have hWi : wMask i = spanMask (wData[i]! % 64) (wData[i]! / 64 % 64) (wData[i]! / 4096) := rfl
  have hWj : wMask j = spanMask (wData[j]! % 64) (wData[j]! / 64 % 64) (wData[j]! / 4096) := rfl
  have hAi : annK i = annMaskOf (wData[i]! % 64) (wData[i]! / 64 % 64) (wData[i]! / 4096) := rfl
  have hAj : annK j = annMaskOf (wData[j]! % 64) (wData[j]! / 64 % 64) (wData[j]! / 4096) := rfl
  have xi := xorClosed_span ai bi ci
  have xj := xorClosed_span aj bj cj
  have ni := annS_span ai bi ci
  have nj := annS_span aj bj cj
  rw [← hWi] at xi ni
  rw [← hWj] at xj nj
  rw [← hAi] at ni
  rw [← hAj] at nj
  unfold meetCardK
  rw [countMN_eq, setM_and, setM_and, ← ni, ← nj, card_annInter xi xj hci hcj, Nat.pow_two]
  · intro v hv φ hφ hmv hnφ
    rw [Nat.testBit_and, Bool.and_eq_true] at hmv hnφ
    have hv' : v ∈ setM (wMask i) := mem_setM.mpr ⟨hv, hmv.1⟩
    have hφ' : φ ∈ annS (setM (wMask i)) := by
      rw [ni, mem_setM]
      exact ⟨hφ, hnφ.1⟩
    exact (Finset.mem_filter.mp hφ').2 v hv'
  · rw [Nat.testBit_and, Bool.and_eq_true]
    exact ⟨(mem_setM.mp xi.2.1).2, (mem_setM.mp xj.2.1).2⟩
  · rw [Nat.testBit_and, Bool.and_eq_true]
    have z : ∀ A : Finset Nat, (0 : Nat) ∈ annS A := fun A =>
      Finset.mem_filter.mpr ⟨by simp, fun x _ => by unfold form; rw [Nat.zero_and]; rfl⟩
    have zi := z (setM (wMask i))
    have zj := z (setM (wMask j))
    rw [ni, mem_setM] at zi
    rw [nj, mem_setM] at zj
    exact ⟨zi.2, zj.2⟩

end CFSG.SmithL6.K
