module

public import Certificates.Data.Kernel.Misc.Oq
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowSearch
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_zero)

private def stp (s p r : ℕ) : ℕ := if (p ^^^ r) >>> s < p >>> s then p ^^^ r else p

private def red (s : ℕ) (rows : List ℕ) (p : ℕ) : ℕ := rows.foldl (stp s) p

private theorem red_cons (s b : ℕ) (l : List ℕ) (p : ℕ) :
    red s (b :: l) p = red s l (stp s p b) := rfl

private theorem xor_lt_iff (a b : ℕ) : a ^^^ b < a ↔ (b ≠ 0 ∧ a.testBit b.log2 = true) := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hb1 : b.testBit b.log2 = true := Nat.testBit_log2 hb
    have hb2 : ∀ j, b.log2 < j → b.testBit j = false := fun j hj =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.lt_log2_self (n := b))
        (Nat.pow_le_pow_right Nat.two_pos hj))
    cases ha : a.testBit b.log2
    · have : a < a ^^^ b := Nat.lt_of_testBit b.log2 ha (by rw [Nat.testBit_xor, ha, hb1]; rfl)
        (fun j hj => by rw [Nat.testBit_xor, hb2 j hj]; simp)
      simp [hb, ha, not_lt.2 this.le]
    · have : a ^^^ b < a := Nat.lt_of_testBit b.log2 (by rw [Nat.testBit_xor, ha, hb1]; rfl) ha
        (fun j hj => by rw [Nat.testBit_xor, hb2 j hj]; simp)
      simp [hb, this]

private theorem stp_eq (s p r : ℕ) : stp s p r =
    if (r >>> s ≠ 0 ∧ (p >>> s).testBit (r >>> s).log2 = true) then p ^^^ r else p := by
  simp only [stp, Nat.shiftRight_xor_distrib, xor_lt_iff]

private theorem stp_xor (s r p q : ℕ) : stp s (p ^^^ q) r = stp s p r ^^^ stp s q r := by
  by_cases hb : r >>> s = 0
  · simp [stp_eq, hb]
  · cases hp : (p >>> s).testBit (r >>> s).log2 <;> cases hq : (q >>> s).testBit (r >>> s).log2 <;>
      simp [stp_eq, hb, hp, hq, Nat.shiftRight_xor_distrib, Nat.testBit_xor, Nat.xor_assoc,
        Nat.xor_comm, Nat.xor_left_comm]

private theorem stp_zero (s r : ℕ) : stp s 0 r = 0 := by
  simp [stp_eq]

private theorem red_xor (s : ℕ) (rows : List ℕ) :
    ∀ p q, red s rows (p ^^^ q) = red s rows p ^^^ red s rows q := by
  induction rows with
  | nil => intro p q; rfl
  | cons r rs ih => intro p q; simp only [red, List.foldl_cons] at ih ⊢; rw [stp_xor, ih]

private theorem red_zero (s : ℕ) (rows : List ℕ) : red s rows 0 = 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp only [red, List.foldl_cons] at ih ⊢; rw [stp_zero, ih]

private inductive SpN (L : List ℕ) : ℕ → Prop
  | zero : SpN L 0
  | mem {x : ℕ} : x ∈ L → SpN L x
  | xor {a b : ℕ} : SpN L a → SpN L b → SpN L (a ^^^ b)

private theorem SpN.mono {L L' : List ℕ} (h : ∀ x ∈ L, x ∈ L') {z : ℕ} (hz : SpN L z) :
    SpN L' z := by
  induction hz with
  | zero => exact SpN.zero
  | mem hx => exact SpN.mem (h _ hx)
  | xor _ _ ih1 ih2 => exact SpN.xor ih1 ih2

private theorem red_sp (s : ℕ) (rows : List ℕ) :
    ∀ p, ∃ w, SpN rows w ∧ red s rows p = p ^^^ w := by
  induction rows with
  | nil => intro p; exact ⟨0, SpN.zero, by simp [red]⟩
  | cons r rs ih =>
    intro p
    obtain ⟨w, hw, h⟩ := ih (stp s p r)
    have hw' : SpN (r :: rs) w := hw.mono fun x hx => List.mem_cons_of_mem _ hx
    simp only [red, List.foldl_cons] at h ⊢
    rw [h, stp_eq]
    split
    · exact ⟨r ^^^ w, SpN.xor (SpN.mem List.mem_cons_self) hw', by
        simp [Nat.xor_assoc]⟩
    · exact ⟨w, hw', rfl⟩

private def Ech (s : ℕ) (rows : List ℕ) : Prop :=
  (∀ r ∈ rows, r >>> s ≠ 0) ∧ rows.Pairwise fun a b => b >>> s < 2 ^ (a >>> s).log2

private theorem Ech.cons {s : ℕ} {b : ℕ} {l : List ℕ} (h : Ech s (b :: l)) :
    b >>> s ≠ 0 ∧ Ech s l ∧ ∀ x ∈ l, x >>> s < 2 ^ (b >>> s).log2 := by
  obtain ⟨h1, h2⟩ := h
  rw [List.pairwise_cons] at h2
  exact ⟨h1 b List.mem_cons_self, ⟨fun r hr => h1 r (List.mem_cons_of_mem _ hr), h2.2⟩, h2.1⟩

private theorem red_mem (s : ℕ) (rows : List ℕ) (h : Ech s rows) :
    ∀ r ∈ rows, red s rows r = 0 := by
  induction rows with
  | nil => intro r hr; exact absurd hr List.not_mem_nil
  | cons b l ih =>
    intro r hr
    obtain ⟨hb, hl, hlt⟩ := h.cons
    simp only [red, List.foldl_cons]
    rcases List.mem_cons.1 hr with rfl | hr
    · have : stp s r r = 0 := by
        rw [stp_eq, if_pos ⟨hb, by simpa using Nat.testBit_log2 hb⟩]
        exact Nat.xor_self _
      rw [this]
      exact red_zero s l
    · have : stp s r b = r := by
        rw [stp_eq, if_neg]
        rintro ⟨-, h2⟩
        rw [Nat.testBit_lt_two_pow (hlt r hr)] at h2
        exact Bool.false_ne_true h2
      rw [this]
      exact ih hl r hr

private theorem red_high (s h : ℕ) (rows : List ℕ) (hr : ∀ x ∈ rows, x >>> s < 2 ^ h) (j : ℕ)
    (hj : h ≤ j) : ∀ p, (red s rows p >>> s).testBit j = (p >>> s).testBit j := by
  induction rows with
  | nil => intro p; rfl
  | cons x l ih =>
    intro p
    simp only [red, List.foldl_cons]
    have ih' := ih (fun y hy => hr y (List.mem_cons_of_mem _ hy)) (stp s p x)
    simp only [red] at ih'
    rw [ih', stp_eq]
    split
    · rw [Nat.shiftRight_xor_distrib, Nat.testBit_xor,
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hr x List.mem_cons_self)
          (Nat.pow_le_pow_right Nat.two_pos hj))]
      simp
    · rfl

private theorem red_clears (s : ℕ) (rows : List ℕ) (h : Ech s rows) :
    ∀ p, ∀ r ∈ rows, (red s rows p >>> s).testBit (r >>> s).log2 = false := by
  induction rows with
  | nil => intro p r hr; exact absurd hr List.not_mem_nil
  | cons b l ih =>
    intro p r hr
    obtain ⟨hb, hl, hlt⟩ := h.cons
    rcases List.mem_cons.1 hr with rfl | hr
    · simp only [red, List.foldl_cons]
      have := red_high s (r >>> s).log2 l hlt (r >>> s).log2 le_rfl (stp s p r)
      simp only [red] at this
      rw [this, stp_eq]
      split
      · rename_i hc
        rw [Nat.shiftRight_xor_distrib, Nat.testBit_xor, hc.2, Nat.testBit_log2 hb]
        rfl
      · rename_i hc
        have : ¬ (r >>> s ≠ 0 ∧ (p >>> s).testBit (r >>> s).log2 = true) := hc
        simpa [hb] using this
    · rw [red_cons]
      exact ih hl _ r hr

private theorem red_of_sp (s : ℕ) (rows : List ℕ) (h : Ech s rows) {w : ℕ} (hw : SpN rows w) :
    red s rows w = 0 := by
  induction hw with
  | zero => exact red_zero s rows
  | mem hx => exact red_mem s rows h _ hx
  | xor _ _ ih1 ih2 => rw [red_xor, ih1, ih2]; rfl

private def oins (s p : ℕ) (rows : List ℕ) : List ℕ :=
  rows.orderedInsert (fun a b => b >>> s ≤ a >>> s) p

private theorem lt_pow_of_clear {x h : ℕ} (hx : x < 2 ^ (h + 1)) (hb : x.testBit h = false) :
    x < 2 ^ h := by
  refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hb
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right Nat.two_pos hj))

private theorem log2_lt_of_clear {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hle : b ≤ a)
    (hc : a.testBit b.log2 = false) : b.log2 < a.log2 := by
  have h1 : b.log2 < a.log2 + 1 := (Nat.log2_lt hb).2 (lt_of_le_of_lt hle Nat.lt_log2_self)
  rcases Nat.lt_or_ge b.log2 a.log2 with h | h
  · exact h
  · have : b.log2 = a.log2 := by omega
    rw [this, Nat.testBit_log2 ha] at hc
    exact absurd hc (by simp)

private theorem Ech_oins (s p : ℕ) {rows : List ℕ} (h : Ech s rows) (hp : p >>> s ≠ 0)
    (hc : ∀ r ∈ rows, (p >>> s).testBit (r >>> s).log2 = false) : Ech s (oins s p rows) := by
  induction rows with
  | nil =>
    simp only [oins, List.orderedInsert_nil]
    exact ⟨fun r hr => by rw [List.mem_singleton.1 hr]; exact hp, List.pairwise_singleton _ _⟩
  | cons b l ih =>
    obtain ⟨hb, hl, hlt⟩ := h.cons
    have hcb := hc b List.mem_cons_self
    have hcl : ∀ r ∈ l, (p >>> s).testBit (r >>> s).log2 = false :=
      fun r hr => hc r (List.mem_cons_of_mem _ hr)
    have hne : ∀ x ∈ b :: l, x >>> s ≠ 0 := h.1
    simp only [oins, List.orderedInsert_cons]
    split
    · rename_i hle
      have hlog : (b >>> s).log2 < (p >>> s).log2 := log2_lt_of_clear hp hb hle hcb
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact hp
        · exact hne r hr
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, h.2⟩
        have hpow : 2 ^ ((b >>> s).log2 + 1) ≤ 2 ^ (p >>> s).log2 :=
          Nat.pow_le_pow_right Nat.two_pos hlog
        rcases List.mem_cons.1 hx with rfl | hx
        · exact lt_of_lt_of_le Nat.lt_log2_self hpow
        · exact lt_of_lt_of_le (hlt x hx)
            (le_trans (Nat.pow_le_pow_right Nat.two_pos (Nat.le_succ _)) hpow)
    · rename_i hlt'
      have ih' := ih hl hcl
      have hmem : ∀ x ∈ oins s p l, x = p ∨ x ∈ l := fun x hx =>
        (List.mem_orderedInsert _).1 hx
      refine ⟨fun r hr => ?_, ?_⟩
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact hb
        · rcases hmem r hr with rfl | hr
          · exact hp
          · exact hl.1 r hr
      · rw [List.pairwise_cons]
        refine ⟨fun x hx => ?_, ih'.2⟩
        rcases hmem x hx with rfl | hx
        · exact lt_pow_of_clear (lt_trans (not_le.1 hlt') Nat.lt_log2_self) hcb
        · exact hlt x hx

private theorem lmRedK_letN (y : ℕ) (k : ℕ → ℕ) : lmRedK.letN y k = k y := by
  cases y <;> rfl

private theorem lmRedK_eq (rows : List ℕ) : ∀ p, lmRedK rows p = red 9 rows p := by
  induction rows with
  | nil => intro p; rfl
  | cons r rs ih =>
    intro p
    rw [red_cons, ← ih]
    have : lmRedK (r :: rs) p = lmRedK.letN (Nat.xor p r) (fun q => lmRedK rs
        (Bool.rec (motive := fun _ => Nat) p q (Nat.blt (Nat.shiftRight q 9) (Nat.shiftRight p 9)))) :=
      rfl
    rw [this, lmRedK_letN]
    congr 1
    unfold stp
    cases h : Nat.blt (Nat.shiftRight (Nat.xor p r) 9) (Nat.shiftRight p 9)
    · have : ¬ ((p ^^^ r) >>> 9 < p >>> 9) := by
        intro hlt
        have h2 : Nat.blt (Nat.shiftRight (Nat.xor p r) 9) (Nat.shiftRight p 9) = true :=
          Nat.blt_eq ▸ hlt
        rw [h] at h2; exact absurd h2 (by decide)
      simp [this]
    · have : (p ^^^ r) >>> 9 < p >>> 9 := by
        have := h; rw [Nat.blt_eq] at this; exact this
      simp [this]

private theorem redV_eq (ib : List ℕ) : ∀ a, redV ib a = red 0 ib a := by
  induction ib with
  | nil => intro a; rfl
  | cons b l ih =>
    intro a
    rw [red_cons, ← ih]
    show redV l (Bool.rec (motive := fun _ => Nat) a (Nat.xor a b) (Nat.blt (Nat.xor a b) a)) = _
    congr 1
    unfold stp
    simp only [Nat.shiftRight_zero]
    cases h : Nat.blt (Nat.xor a b) a
    · have : ¬ (a ^^^ b < a) := by
        intro hlt
        have h2 : Nat.blt (Nat.xor a b) a = true := Nat.blt_eq ▸ hlt
        rw [h] at h2; exact absurd h2 (by decide)
      simp [this]
    · have : a ^^^ b < a := by
        have := h; rw [Nat.blt_eq] at this; exact this
      simp [this]

private theorem oinsK_eq (p : ℕ) (rows : List ℕ) : oinsK p rows = oins 9 p rows := by
  induction rows with
  | nil => show List.cons p List.nil = _; simp [oins]
  | cons b l ih =>
    show Bool.rec (motive := fun _ => List Nat) (List.cons b (oinsK p l))
      (List.cons p (List.cons b l)) (Nat.ble (Nat.shiftRight b 9) (Nat.shiftRight p 9)) = _
    unfold oins
    rw [List.orderedInsert_cons]
    cases h : Nat.ble (Nat.shiftRight b 9) (Nat.shiftRight p 9)
    · have : ¬ (b >>> 9 ≤ p >>> 9) := by
        intro hle
        have h2 : Nat.ble (Nat.shiftRight b 9) (Nat.shiftRight p 9) = true := Nat.ble_eq ▸ hle
        rw [h] at h2; exact absurd h2 (by decide)
      rw [if_neg this]
      exact congrArg _ ih
    · have : b >>> 9 ≤ p >>> 9 := by
        have := h; rw [Nat.ble_eq] at this; exact this
      rw [if_pos this]

private theorem insV_eq (a : ℕ) (ib : List ℕ) : insV a ib = oins 0 a ib := by
  induction ib with
  | nil => show List.cons a List.nil = _; simp [oins]
  | cons b l ih =>
    show Bool.rec (motive := fun _ => List Nat) (List.cons b (insV a l))
      (List.cons a (List.cons b l)) (Nat.ble b a) = _
    unfold oins
    rw [List.orderedInsert_cons]
    cases h : Nat.ble b a
    · have : ¬ (b >>> 0 ≤ a >>> 0) := by
        intro hle
        have h2 : Nat.ble b a = true := Nat.ble_eq ▸ hle
        rw [h] at h2; exact absurd h2 (by decide)
      rw [if_neg this]
      exact congrArg _ ih
    · have : b >>> 0 ≤ a >>> 0 := by
        have := h; rw [Nat.ble_eq] at this; exact this
      rw [if_pos this]

private def addP (rows : List ℕ) (P : ℕ) : Option (List ℕ) :=
  if P >>> 9 = 0 then (if P &&& 511 = 0 then some rows else none) else some (oins 9 P rows)

private theorem lmAddK_letO (y : ℕ) (k : ℕ → Option (List ℕ)) : lmAddK.letO y k = k y := by
  cases y <;> rfl

private theorem lmAddK_eq (rows : List ℕ) (x y : ℕ) :
    lmAddK rows x y = addP rows (red 9 rows (x * 512 + y)) := by
  have : lmAddK rows x y = lmAddK.letO (lmRedK rows (Nat.add (Nat.mul x 512) y)) fun p =>
      Bool.rec (motive := fun _ => Option (List Nat)) (some (oinsK p rows))
        (Bool.rec (motive := fun _ => Option (List Nat)) none (some rows) (Nat.beq (Nat.land p 511) 0))
        (Nat.beq (Nat.shiftRight p 9) 0) := rfl
  rw [this, lmAddK_letO, lmRedK_eq]
  show _ = addP rows _
  generalize red 9 rows (x * 512 + y) = P
  unfold addP
  rw [oinsK_eq]
  by_cases h1 : P >>> 9 = 0
  · have h1' : Nat.beq (Nat.shiftRight P 9) 0 = true := Nat.beq_eq ▸ h1
    rw [h1', if_pos h1]
    by_cases h2 : P &&& 511 = 0
    · have h2' : Nat.beq (Nat.land P 511) 0 = true := Nat.beq_eq ▸ h2
      rw [h2', if_pos h2]
    · have h2' : Nat.beq (Nat.land P 511) 0 = false := by
        cases h : Nat.beq (Nat.land P 511) 0
        · rfl
        · exact absurd (Nat.beq_eq ▸ h) h2
      rw [h2', if_neg h2]
  · have h1' : Nat.beq (Nat.shiftRight P 9) 0 = false := by
      cases h : Nat.beq (Nat.shiftRight P 9) 0
      · rfl
      · exact absurd (Nat.beq_eq ▸ h) h1
    rw [h1', if_neg h1]

private theorem addP_spec {rows rows' : List ℕ} {P z : ℕ} (hE : Ech 9 rows)
    (hP : red 9 rows z = P) (h : addP rows P = some rows') :
    Ech 9 rows' ∧ (∀ x ∈ rows, x ∈ rows') ∧ SpN rows' z := by
  obtain ⟨w, hw, hPw⟩ := red_sp 9 rows z
  rw [hP] at hPw
  have hz : z = P ^^^ w := by rw [hPw, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  unfold addP at h
  by_cases h1 : P >>> 9 = 0
  · rw [if_pos h1] at h
    by_cases h2 : P &&& 511 = 0
    · rw [if_pos h2] at h
      cases h
      have hP0 : P = 0 := by
        refine Nat.eq_of_testBit_eq fun i => ?_
        rw [Nat.zero_testBit]
        by_cases hi : i < 9
        · have h511 : (511 : ℕ) = 2 ^ 9 - 1 := rfl
          rw [h511] at h2
          have := congrArg (fun n => n.testBit i) h2
          simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
            decide_eq_true hi, Bool.and_true] at this
          exact this
        · have := congrArg (fun n => n.testBit (i - 9)) h1
          simpa [Nat.testBit_shiftRight, show 9 + (i - 9) = i by omega] using this
      refine ⟨hE, fun x hx => hx, ?_⟩
      rw [hz, hP0, Nat.zero_xor]
      exact hw
    · rw [if_neg h2] at h
      exact absurd h (by simp)
  · rw [if_neg h1] at h
    cases h
    have hmem : ∀ x ∈ rows, x ∈ oins 9 P rows := fun x hx =>
      (List.mem_orderedInsert _).2 (Or.inr hx)
    refine ⟨Ech_oins 9 P hE h1 (fun r hr => ?_), hmem, ?_⟩
    · have := red_clears 9 rows hE z r hr
      rw [hP] at this
      exact this
    · rw [hz]
      exact SpN.xor (SpN.mem ((List.mem_orderedInsert _).2 (Or.inl rfl))) (hw.mono hmem)

private theorem wpart_xor : ∀ v < 64, ∀ w < 64, wpart (v ^^^ w) = wpart v ^^^ wpart w := by decide +kernel

private theorem xpart_xor : ∀ v < 64, ∀ w < 64, xpart (v ^^^ w) = xpart v ^^^ xpart w := by decide +kernel

private theorem wpart_lt (v : ℕ) (hv : v < 64) : wpart v < 8 := by
  revert v; decide +kernel

private theorem xpart_lt (v : ℕ) (hv : v < 64) : xpart v < 8 := by
  revert v; decide +kernel

private theorem outer_xor_left : ∀ a < 8, ∀ a' < 8, ∀ b < 8,
    outer (a ^^^ a') b = outer a b ^^^ outer a' b := by decide +kernel

private theorem outer_xor_right : ∀ a < 8, ∀ b < 8, ∀ b' < 8,
    outer a (b ^^^ b') = outer a b ^^^ outer a b' := by decide +kernel

private theorem pk_xor {a b c d : ℕ} (hb : b < 512) (hd : d < 512) :
    (a * 512 + b) ^^^ (c * 512 + d) = (a ^^^ c) * 512 + (b ^^^ d) := by
  have h : ∀ a b : ℕ, b < 512 → a * 512 + b = 2 ^ 9 * a + b := fun a b _ => by
    rw [Nat.mul_comm]; rfl
  rw [h a b hb, h c d hd, h (a ^^^ c) (b ^^^ d) (Nat.xor_lt_two_pow (n := 9) hb hd)]
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add a hb, Nat.testBit_two_pow_mul_add c hd,
    Nat.testBit_two_pow_mul_add (a ^^^ c) (Nat.xor_lt_two_pow (n := 9) hb hd)]
  split
  · rw [Nat.testBit_xor]
  · rw [Nat.testBit_xor]

private def qq (u : Bool) (a b : ℕ) : ℕ :=
  outer a a ^^^ outer a b ^^^ (if u then outer b b else 0)

private def BBp (u : Bool) (a b c d : ℕ) : ℕ :=
  outer a c ^^^ outer c a ^^^ outer a d ^^^ outer c b ^^^
    (if u then outer b d ^^^ outer d b else 0)

private theorem qq_key : ∀ u : Bool, ∀ a < 8, ∀ b < 8, ∀ c < 8, ∀ d < 8,
    qq u (a ^^^ c) (b ^^^ d) ^^^ qq u a b ^^^ qq u c d = BBp u a b c d := by decide +kernel

private theorem beta_eq (u : Bool) {v w : ℕ} (hv : v < 64) (hw : w < 64) :
    betaOf u v w = BBp u (wpart v) (xpart v) (wpart w) (xpart w) := by
  have h := qq_key u _ (wpart_lt v hv) _ (xpart_lt v hv) _ (wpart_lt w hw) _ (xpart_lt w hw)
  rw [← h]
  unfold betaOf qOf qq
  rw [wpart_xor v hv w hw, xpart_xor v hv w hw]

private theorem BBp_add_left (u : Bool) {a a' b b' c d : ℕ} (ha : a < 8) (ha' : a' < 8)
    (hb : b < 8) (hb' : b' < 8) (hc : c < 8) (hd : d < 8) :
    BBp u (a ^^^ a') (b ^^^ b') c d = BBp u a b c d ^^^ BBp u a' b' c d := by
  unfold BBp
  rw [outer_xor_left a ha a' ha' c hc, outer_xor_right c hc a ha a' ha',
    outer_xor_left a ha a' ha' d hd, outer_xor_right c hc b hb b' hb',
    outer_xor_left b hb b' hb' d hd, outer_xor_right d hd b hb b' hb']
  cases u <;> simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

private theorem beta_add_left (u : Bool) {x x' y : ℕ} (hx : x < 64) (hx' : x' < 64) (hy : y < 64) :
    betaOf u (x ^^^ x') y = betaOf u x y ^^^ betaOf u x' y := by
  have hxx : x ^^^ x' < 64 := Nat.xor_lt_two_pow (n := 6) hx hx'
  rw [beta_eq u hxx hy, beta_eq u hx hy, beta_eq u hx' hy, wpart_xor x hx x' hx',
    xpart_xor x hx x' hx']
  exact BBp_add_left u (wpart_lt x hx) (wpart_lt x' hx') (xpart_lt x hx) (xpart_lt x' hx')
    (wpart_lt y hy) (xpart_lt y hy)

private theorem xorBits_xorP (n : ℕ) (f : ℕ → ℕ) (v w : ℕ) :
    xorBits n f (v ^^^ w) = xorBits n f v ^^^ xorBits n f w := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, xorBits_succ, ih, Nat.testBit_xor]
    cases v.testBit n <;> cases w.testBit n <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

private theorem evalV_xorP (l : List ℕ) (v w : ℕ) :
    evalV l (v ^^^ w) = evalV l v ^^^ evalV l w :=
  xorBits_xorP 6 _ v w

private theorem evalV_zeroP (l : List ℕ) : evalV l 0 = 0 := by
  have := evalV_xorP l 0 0
  rw [Nat.xor_self, Nat.xor_self] at this
  exact this

private theorem xorBits_two_pow_singleP {n j : ℕ} (f : ℕ → ℕ) (hj : j < n) :
    xorBits n f (2 ^ j) = f j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [xorBits_succ, Nat.testBit_two_pow]
    by_cases hjn : j = n
    · subst hjn
      have h0 : xorBits j f (2 ^ j) = 0 := by
        have key : ∀ m, m ≤ j → xorBits m f (2 ^ j) = 0 := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ihm =>
            rw [xorBits_succ, ihm (by omega), Nat.testBit_two_pow]
            simp [show j ≠ m by omega]
        exact key j le_rfl
      simp [h0]
    · rw [ih (by omega)]
      simp [hjn]

private theorem evalV_two_powP {l : List ℕ} {j : ℕ} (hj : j < 6) : evalV l (2 ^ j) = l.getD j 0 :=
  xorBits_two_pow_singleP _ hj

private theorem evalV_ltP {l : List ℕ} (hl : ∀ a ∈ l, a < 64) (v : ℕ) : evalV l v < 64 := by
  have h := CFSG.EvenSmallLie.OmegaEight.SpBranch.xorBits_lt (n := 6)
    (f := fun j => l.getD j 0) (fun j _ => by
      rw [List.getD_eq_getElem?_getD]
      rcases h : l[j]? with _ | a
      · simp
      · exact hl a (List.mem_of_getElem? h)) v
  exact h

private theorem two_pow_add_eq_xor {k w : ℕ} (hw : w < 2 ^ k) : 2 ^ k + w = 2 ^ k ^^^ w := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  have := Nat.testBit_two_pow_mul_add 1 hw j
  rw [Nat.mul_one] at this
  rw [this]
  by_cases hj : j < k
  · simp [hj, show k ≠ j by omega]
  · simp only [hj, if_false, testBit_eq_false_of_lt hw (not_lt.1 hj)]
    by_cases hjk : j = k
    · subst hjk; simp
    · have : (1 : ℕ).testBit (j - k) = false := by
        have hpos : 1 ≤ j - k := by omega
        exact Nat.testBit_lt_two_pow (by
          calc (1 : ℕ) < 2 ^ 1 := by decide
            _ ≤ 2 ^ (j - k) := Nat.pow_le_pow_right Nat.two_pos hpos)
      simp [this, show k ≠ j by omega]

private theorem evalV_append_lt {l : List ℕ} {a v k : ℕ} (hlen : l.length = k) (hv : v < 2 ^ k) :
    evalV (l ++ [a]) v = evalV l v := by
  unfold evalV
  refine xorBits_congr_bits fun j hj hbit => ?_
  have hjk : j < k := by
    by_contra hjk
    rw [testBit_eq_false_of_lt hv (by omega)] at hbit
    exact Bool.false_ne_true hbit
  rw [List.getD_append _ _ _ _ (by omega)]

private theorem evalV_append {l : List ℕ} {a v k : ℕ} (hlen : l.length = k) (hk : k < 6)
    (hv : v < 2 ^ k) : evalV (l ++ [a]) (2 ^ k + v) = a ^^^ evalV l v := by
  rw [two_pow_add_eq_xor hv, evalV_xorP, evalV_two_powP hk, evalV_append_lt hlen hv,
    ← hlen, List.getD_append_right _ _ _ _ le_rfl]
  simp

private def rawv (u : Bool) (l : List ℕ) (v : ℕ) : ℕ := qOf u v * 512 + qOf u (evalV l v)

private def bil (u : Bool) (l : List ℕ) (x y : ℕ) : ℕ :=
  rawv u l (x ^^^ y) ^^^ rawv u l x ^^^ rawv u l y

private theorem betaOf_lt (u : Bool) (v w : ℕ) : betaOf u v w < 512 :=
  Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (n := 9) (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _)

private theorem bil_eq (u : Bool) (l : List ℕ) (x y : ℕ) :
    bil u l x y = betaOf u x y * 512 + betaOf u (evalV l x) (evalV l y) := by
  unfold bil rawv betaOf
  rw [evalV_xorP, pk_xor (qOf_lt u _) (qOf_lt u _),
    pk_xor (Nat.xor_lt_two_pow (n := 9) (qOf_lt u _) (qOf_lt u _)) (qOf_lt u _)]

private theorem bil_add_left (u : Bool) {l : List ℕ} (hl : ∀ a ∈ l, a < 64) {x x' y : ℕ}
    (hx : x < 64) (hx' : x' < 64) (hy : y < 64) :
    bil u l (x ^^^ x') y = bil u l x y ^^^ bil u l x' y := by
  rw [bil_eq, bil_eq, bil_eq, evalV_xorP, beta_add_left u hx hx' hy,
    beta_add_left u (evalV_ltP hl x) (evalV_ltP hl x') (evalV_ltP hl y),
    pk_xor (betaOf_lt u _ _) (betaOf_lt u _ _)]

private def pk (r : ℕ × ℕ) : ℕ := r.1 * 512 + r.2

private theorem pk_shift {p : ℕ × ℕ} (h : p.2 < 512) : pk p >>> 9 = p.1 := by
  rw [Nat.shiftRight_eq_div_pow]
  show (p.1 * 512 + p.2) / 2 ^ 9 = p.1
  have : (2 : ℕ) ^ 9 = 512 := rfl
  rw [this]; omega

private theorem pk_land {p : ℕ × ℕ} (h : p.2 < 512) : pk p &&& 511 = p.2 := by
  have h511 : (511 : ℕ) = 2 ^ 9 - 1 := rfl
  rw [h511, Nat.and_two_pow_sub_one_eq_mod]
  show (p.1 * 512 + p.2) % 2 ^ 9 = p.2
  have : (2 : ℕ) ^ 9 = 512 := rfl
  rw [this]; omega

private theorem pk_xor' {p r : ℕ × ℕ} (hp : p.2 < 512) (hr : r.2 < 512) :
    pk p ^^^ pk r = pk (p.1 ^^^ r.1, p.2 ^^^ r.2) :=
  pk_xor hp hr

private theorem lmRed_pk : ∀ (rows : List (ℕ × ℕ)), (∀ r ∈ rows, r.2 < 512) → ∀ p : ℕ × ℕ,
    p.2 < 512 → red 9 (rows.map pk) (pk p) = pk (lmRed rows p) ∧ (lmRed rows p).2 < 512 := by
  intro rows
  induction rows with
  | nil => intro _ p hp; exact ⟨rfl, hp⟩
  | cons r rs ih =>
    intro hr p hp
    have hr' : r.2 < 512 := hr r List.mem_cons_self
    have hrs : ∀ x ∈ rs, x.2 < 512 := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, red_cons]
    have hlm : lmRed (r :: rs) p = lmRed rs (if p.1 ^^^ r.1 < p.1 then (p.1 ^^^ r.1, p.2 ^^^ r.2)
        else p) := rfl
    rw [hlm]
    have hx : (p.2 ^^^ r.2) < 512 := Nat.xor_lt_two_pow (n := 9) hp hr'
    by_cases hc : p.1 ^^^ r.1 < p.1
    · rw [if_pos hc]
      have : stp 9 (pk p) (pk r) = pk (p.1 ^^^ r.1, p.2 ^^^ r.2) := by
        unfold stp
        rw [pk_xor' hp hr', pk_shift hx, pk_shift hp, if_pos hc]
      rw [this]
      exact ih hrs _ hx
    · rw [if_neg hc]
      have : stp 9 (pk p) (pk r) = pk p := by
        unfold stp
        rw [pk_xor' hp hr', pk_shift hx, pk_shift hp, if_neg hc]
      rw [this]
      exact ih hrs _ hp

private theorem oins_pk : ∀ (rows : List (ℕ × ℕ)), (∀ r ∈ rows, r.2 < 512) → ∀ p : ℕ × ℕ,
    p.2 < 512 → oins 9 (pk p) (rows.map pk) =
      (rows.orderedInsert (fun a b => b.1 ≤ a.1) p).map pk := by
  intro rows
  induction rows with
  | nil => intro _ p _; simp [oins]
  | cons b l ih =>
    intro hr p hp
    have hb : b.2 < 512 := hr b List.mem_cons_self
    have hl : ∀ x ∈ l, x.2 < 512 := fun x hx => hr x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons]
    unfold oins at ih ⊢
    rw [List.orderedInsert_cons, List.orderedInsert_cons, pk_shift hb, pk_shift hp]
    split
    · simp
    · rw [List.map_cons, ih hl p hp]

private theorem lmAdd_pk {rows : List (ℕ × ℕ)} (hr : ∀ r ∈ rows, r.2 < 512) {x y : ℕ}
    (hy : y < 512) :
    (lmAdd rows x y).map (List.map pk) = lmAddK (rows.map pk) x y ∧
      ∀ rs, lmAdd rows x y = some rs → ∀ r ∈ rs, r.2 < 512 := by
  have h := lmRed_pk rows hr (x, y) hy
  rw [lmAddK_eq]
  have hpk : x * 512 + y = pk (x, y) := rfl
  rw [hpk, h.1]
  generalize hp : lmRed rows (x, y) = p at h
  have hp2 : p.2 < 512 := h.2
  unfold lmAdd
  simp only [hp]
  unfold addP
  rw [pk_shift hp2, pk_land hp2]
  by_cases h1 : p.1 = 0
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : p.2 = 0
    · simp only [h2, if_true, Option.map_some]
      exact ⟨trivial, fun rs hrs => by cases hrs; exact hr⟩
    · simp [h2]
  · rw [if_neg h1, if_neg h1]
    refine ⟨?_, ?_⟩
    · simp only [Option.map_some, oins_pk rows hr p hp2]
    · intro rs hrs r hrm
      simp only [Option.some.injEq] at hrs
      subst hrs
      rcases (List.mem_orderedInsert _).1 hrm with rfl | hrm
      · exact hp2
      · exact hr r hrm

private theorem qOf_zero (u : Bool) : qOf u 0 = 0 := by
  cases u <;> decide

private theorem two_pow_add_eq_xor' {k w : ℕ} (hw : w < 2 ^ k) : w ^^^ 2 ^ k = 2 ^ k + w := by
  rw [two_pow_add_eq_xor hw, Nat.xor_comm]

private theorem rawv_zero (u : Bool) (l : List ℕ) : rawv u l 0 = 0 := by
  unfold rawv; rw [evalV_zeroP, qOf_zero]

private theorem rawv_xor (u : Bool) (l : List ℕ) (x y : ℕ) :
    rawv u l (x ^^^ y) = bil u l x y ^^^ rawv u l x ^^^ rawv u l y := by
  unfold bil
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_xor]
  cases (rawv u l (x ^^^ y)).testBit i <;> cases (rawv u l x).testBit i <;>
    cases (rawv u l y).testBit i <;> rfl

private theorem rawv_append_lt {u : Bool} {l : List ℕ} {a v k : ℕ} (hlen : l.length = k)
    (hv : v < 2 ^ k) : rawv u (l ++ [a]) v = rawv u l v := by
  unfold rawv; rw [evalV_append_lt hlen hv]

private noncomputable def stepK (u : Bool) (l : List ℕ) (k : ℕ) (acc : Option (List ℕ)) (w : ℕ) :
    Option (List ℕ) :=
  acc.bind fun rs => if evalV l (2 ^ k + w) = 0 then none
    else lmAddK rs (qOf u (2 ^ k + w)) (qOf u (evalV l (2 ^ k + w)))

private noncomputable def genF (u : Bool) (imgs : List ℕ) (k a : ℕ) (rows : List ℕ) : ℕ → Option (List ℕ)
  | 0 => lmAddK rows (qOf u (2 ^ k)) (qOf u a)
  | j + 1 => (genF u imgs k a rows j).bind fun rs =>
      lmAddK rs (betaOf u (2 ^ k) (2 ^ j)) (betaOf u a (imgs.getD j 0))

private theorem foldl_stepK_none (u : Bool) (l : List ℕ) (k : ℕ) (L : List ℕ) :
    L.foldl (stepK u l k) none = none := by
  induction L with
  | nil => rfl
  | cons x t ih => rw [List.foldl_cons]; exact ih

private theorem foldl_stepK_const (u : Bool) (l : List ℕ) (k : ℕ) (r : List ℕ) (L : List ℕ)
    (h : ∀ x ∈ L, stepK u l k (some r) x = some r) : L.foldl (stepK u l k) (some r) = some r := by
  induction L with
  | nil => rfl
  | cons x t ih =>
    rw [List.foldl_cons, h x List.mem_cons_self]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

private theorem addP_zero (rows : List ℕ) : addP rows 0 = some rows := by
  simp [addP]

private def GoodD (u : Bool) (l : List ℕ) (k : ℕ) (rows : List ℕ) (m : ℕ)
    (o : Option (List ℕ)) : Prop :=
  ∀ rows', o = some rows' → Ech 9 rows' ∧ (∀ x ∈ rows, x ∈ rows') ∧
    ∀ w < 2 ^ m, SpN rows' (rawv u l (2 ^ k + w))

private theorem foldD (u : Bool) (imgs : List ℕ) (a k : ℕ) (hlen : imgs.length = k) (hk : k < 6)
    (himgs : ∀ x ∈ imgs, x < 64) (ha : a < 64)
    (hindep : ∀ w < 2 ^ k, a ^^^ evalV imgs w ≠ 0)
    (rows : List ℕ) (hE : Ech 9 rows) (hZ : ∀ v < 2 ^ k, SpN rows (rawv u imgs v)) :
    ∀ m, m ≤ k → (List.range (2 ^ m)).foldl (stepK u (imgs ++ [a]) k) (some rows) =
        genF u imgs k a rows m ∧
      GoodD u (imgs ++ [a]) k rows m (genF u imgs k a rows m) := by
  have hl : ∀ x ∈ imgs ++ [a], x < 64 := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact himgs x hx
    · rw [List.mem_singleton.1 hx]; exact ha
  have hnz : ∀ w < 2 ^ k, evalV (imgs ++ [a]) (2 ^ k + w) ≠ 0 := fun w hw => by
    rw [evalV_append hlen hk hw]; exact hindep w hw
  have hk64 : 2 ^ k < 64 :=
    calc 2 ^ k < 2 ^ 6 := Nat.pow_lt_pow_right Nat.one_lt_two hk
      _ = 64 := rfl
  intro m
  induction m with
  | zero =>
    intro _
    have h0 : evalV (imgs ++ [a]) (2 ^ k + 0) = a := by
      rw [evalV_append hlen hk (Nat.two_pow_pos k), evalV_zeroP, Nat.xor_zero]
    have hne := hnz 0 (Nat.two_pow_pos k)
    have hg0 : genF u imgs k a rows 0 = lmAddK rows (qOf u (2 ^ k)) (qOf u a) := rfl
    have hfold : (List.range (2 ^ 0)).foldl (stepK u (imgs ++ [a]) k) (some rows) =
        lmAddK rows (qOf u (2 ^ k)) (qOf u a) := by
      show (List.range 1).foldl _ _ = _
      simp only [List.range_one, List.foldl_cons, List.foldl_nil]
      unfold stepK
      rw [Option.bind_some, if_neg hne, h0, Nat.add_zero]
    refine ⟨hfold.trans hg0.symm, fun rows' h => ?_⟩
    rw [hg0, lmAddK_eq] at h
    obtain ⟨h1, h2, h3⟩ := addP_spec hE rfl h
    refine ⟨h1, h2, fun w hw => ?_⟩
    have : w = 0 := by omega
    subst this
    unfold rawv
    rw [h0, Nat.add_zero]
    exact h3
  | succ m ih =>
    intro hm
    obtain ⟨hfold, hgood⟩ := ih (by omega)
    have hmk : m < k := by omega
    have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    have hpowk : 2 ^ m + 2 ^ m ≤ 2 ^ k := by
      rw [← hpow]; exact Nat.pow_le_pow_right Nat.two_pos hmk
    have hrange : List.range (2 ^ (m + 1)) =
        List.range (2 ^ m) ++ (List.range (2 ^ m)).map (fun x => 2 ^ m + x) := by
      rw [hpow, List.range_add]
    have hgs : genF u imgs k a rows (m + 1) = (genF u imgs k a rows m).bind fun rs =>
        lmAddK rs (betaOf u (2 ^ k) (2 ^ m)) (betaOf u a (imgs.getD m 0)) := rfl
    rw [hrange, List.foldl_append, hfold, hgs]
    rcases hgm : genF u imgs k a rows m with _ | rm
    · rw [Option.bind_none]
      exact ⟨foldl_stepK_none _ _ _ _, fun _ h => by cases h⟩
    · rw [Option.bind_some]
      rw [hgm] at hgood
      have hmpos : 0 < 2 ^ m := Nat.two_pow_pos m
      obtain ⟨hEm, hsub, hSm⟩ := hgood rm rfl
      have hZm : ∀ v < 2 ^ k, SpN rm (rawv u imgs v) := fun v hv =>
        (hZ v hv).mono hsub
      set genpk : ℕ := betaOf u (2 ^ k) (2 ^ m) * 512 + betaOf u a (imgs.getD m 0) with hgenpk
      have hbilg : bil u (imgs ++ [a]) (2 ^ k) (2 ^ m) = genpk := by
        have h1 : evalV (imgs ++ [a]) (2 ^ k) = a := by
          have := evalV_append (a := a) hlen hk (Nat.two_pow_pos k)
          rwa [Nat.add_zero, evalV_zeroP, Nat.xor_zero] at this
        have h2 : evalV (imgs ++ [a]) (2 ^ m) = imgs.getD m 0 := by
          rw [evalV_two_powP (by omega), List.getD_append _ _ _ _ (by omega)]
        rw [bil_eq, h1, h2]
      have hT : ∀ w < 2 ^ m, SpN rm (bil u (imgs ++ [a]) w (2 ^ m) ^^^
          rawv u (imgs ++ [a]) (2 ^ k + w) ^^^ rawv u (imgs ++ [a]) (2 ^ m)) := by
        intro w hw
        have hwk : w < 2 ^ k := by omega
        have hm2 : w ^^^ 2 ^ m < 2 ^ k := by
          rw [two_pow_add_eq_xor' hw]; omega
        have hmk' : 2 ^ m < 2 ^ k := by omega
        have e1 : rawv u (imgs ++ [a]) w = rawv u imgs w := rawv_append_lt hlen hwk
        have e2 : rawv u (imgs ++ [a]) (2 ^ m) = rawv u imgs (2 ^ m) := rawv_append_lt hlen hmk'
        have e3 : rawv u (imgs ++ [a]) (w ^^^ 2 ^ m) = rawv u imgs (w ^^^ 2 ^ m) :=
          rawv_append_lt hlen hm2
        have hb : bil u (imgs ++ [a]) w (2 ^ m) = rawv u imgs (w ^^^ 2 ^ m) ^^^ rawv u imgs w ^^^
            rawv u imgs (2 ^ m) := by
          unfold bil; rw [e1, e2, e3]
        rw [hb, e2]
        exact SpN.xor (SpN.xor (SpN.xor (SpN.xor (hZm _ hm2) (hZm _ hwk)) (hZm _ hmk')) (hSm w hw))
          (hZm _ hmk')
      have hK1 : ∀ w < 2 ^ m, rawv u (imgs ++ [a]) (2 ^ k + (2 ^ m + w)) =
          genpk ^^^ (bil u (imgs ++ [a]) w (2 ^ m) ^^^ rawv u (imgs ++ [a]) (2 ^ k + w) ^^^
            rawv u (imgs ++ [a]) (2 ^ m)) := by
        intro w hw
        have hwk : w < 2 ^ k := by omega
        have hmk' : 2 ^ m < 2 ^ k := by omega
        have hidx : 2 ^ k + (2 ^ m + w) = (2 ^ k + w) ^^^ 2 ^ m := by
          calc 2 ^ k + (2 ^ m + w) = 2 ^ k ^^^ (2 ^ m + w) := two_pow_add_eq_xor (by omega)
            _ = 2 ^ k ^^^ (w ^^^ 2 ^ m) := by rw [two_pow_add_eq_xor' hw]
            _ = (2 ^ k ^^^ w) ^^^ 2 ^ m := by rw [Nat.xor_assoc]
            _ = (2 ^ k + w) ^^^ 2 ^ m := by rw [two_pow_add_eq_xor hwk]
        have hbil : bil u (imgs ++ [a]) (2 ^ k + w) (2 ^ m) =
            genpk ^^^ bil u (imgs ++ [a]) w (2 ^ m) := by
          rw [two_pow_add_eq_xor hwk, bil_add_left u hl hk64 (by omega) (by omega), hbilg]
        rw [hidx, rawv_xor, hbil]
        simp only [Nat.xor_assoc]
      have hmem : ∀ rr : List ℕ, (∀ x ∈ rm, x ∈ rr) → SpN rr genpk → ∀ w < 2 ^ m,
          SpN rr (rawv u (imgs ++ [a]) (2 ^ k + (2 ^ m + w))) := by
        intro rr hrr hg w hw
        rw [hK1 w hw]
        exact SpN.xor hg ((hT w hw).mono hrr)
      have hstep1 : stepK u (imgs ++ [a]) k (some rm) (2 ^ m + 0) =
          lmAddK rm (betaOf u (2 ^ k) (2 ^ m)) (betaOf u a (imgs.getD m 0)) := by
        unfold stepK
        rw [Option.bind_some, if_neg (hnz _ (by omega)), lmAddK_eq, lmAddK_eq]
        have hz0 : qOf u (2 ^ k + (2 ^ m + 0)) * 512 +
            qOf u (evalV (imgs ++ [a]) (2 ^ k + (2 ^ m + 0))) = genpk ^^^
            (bil u (imgs ++ [a]) 0 (2 ^ m) ^^^ rawv u (imgs ++ [a]) (2 ^ k + 0) ^^^
              rawv u (imgs ++ [a]) (2 ^ m)) := hK1 0 hmpos
        rw [hz0, red_xor, red_of_sp 9 rm hEm (hT 0 (Nat.two_pow_pos m)), Nat.xor_zero]
      have hr0 : List.range (2 ^ m) = 0 :: (List.range (2 ^ m - 1)).map Nat.succ := by
        have h2 : 2 ^ m = (2 ^ m - 1) + 1 := by have := Nat.two_pow_pos m; omega
        conv_lhs => rw [h2]
        exact List.range_succ_eq_map
      rw [hr0]
      simp only [List.map_cons, List.foldl_cons]
      rw [hstep1]
      rcases hR : lmAddK rm (betaOf u (2 ^ k) (2 ^ m)) (betaOf u a (imgs.getD m 0)) with _ | rr
      · exact ⟨foldl_stepK_none _ _ _ _, fun _ h => by cases h⟩
      · have hR' := hR
        rw [lmAddK_eq] at hR'
        obtain ⟨hEr, hrr, hg⟩ := addP_spec hEm (z := genpk) rfl hR'
        have hrest : List.foldl (stepK u (imgs ++ [a]) k) (some rr)
            (List.map (fun x => 2 ^ m + x) (List.map Nat.succ (List.range (2 ^ m - 1)))) =
            some rr := by
          refine foldl_stepK_const _ _ _ _ _ fun x hx => ?_
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
          have hi' : i < 2 ^ m - 1 := List.mem_range.1 hi
          have hw : i.succ < 2 ^ m := by omega
          unfold stepK
          rw [Option.bind_some, if_neg (hnz _ (by omega)), lmAddK_eq]
          have hz := hmem rr hrr hg i.succ hw
          unfold rawv at hz
          rw [red_of_sp 9 rr hEr hz]
          exact addP_zero rr
        rw [hrest]
        refine ⟨rfl, fun rows' h => ?_⟩
        cases h
        refine ⟨hEr, fun x hx => hrr x (hsub x hx), fun w' hw' => ?_⟩
        by_cases hlt : w' < 2 ^ m
        · exact (hSm w' hlt).mono hrr
        · have h2 := hmem rr hrr hg (w' - 2 ^ m) (by omega)
          rwa [Nat.add_sub_cancel' (by omega)] at h2

private theorem fold_dep (u : Bool) (l : List ℕ) (k : ℕ) (L : List ℕ)
    (h : ∃ w ∈ L, evalV l (2 ^ k + w) = 0) :
    ∀ acc, L.foldl (stepK u l k) acc = none := by
  induction L with
  | nil => obtain ⟨w, hw, _⟩ := h; exact absurd hw List.not_mem_nil
  | cons x t ih =>
    intro acc
    rw [List.foldl_cons]
    by_cases hx : evalV l (2 ^ k + x) = 0
    · have : stepK u l k acc x = none := by
        cases acc with
        | none => rfl
        | some rs => simp [stepK, hx]
      rw [this]; exact foldl_stepK_none _ _ _ _
    · obtain ⟨w, hw, hw0⟩ := h
      rcases List.mem_cons.1 hw with rfl | hw
      · exact absurd hw0 hx
      · exact ih ⟨w, hw, hw0⟩ _

private def stepN (u : Bool) (l : List ℕ) (k : ℕ) (acc : Option (List (ℕ × ℕ))) (w : ℕ) :
    Option (List (ℕ × ℕ)) :=
  acc.bind fun rs => if evalV l (2 ^ k + w) = 0 then none
    else lmAdd rs (qOf u (2 ^ k + w)) (qOf u (evalV l (2 ^ k + w)))

private theorem addNew_eq (u : Bool) (l : List ℕ) (k : ℕ) (rows : List (ℕ × ℕ)) :
    addNew u l k rows = (List.range (2 ^ k)).foldl (stepN u l k) (some rows) := rfl

private theorem foldT (u : Bool) (l : List ℕ) (k : ℕ) (L : List ℕ) :
    ∀ acc : Option (List (ℕ × ℕ)), (∀ rs, acc = some rs → ∀ r ∈ rs, r.2 < 512) →
      (L.foldl (stepN u l k) acc).map (List.map pk) =
        L.foldl (stepK u l k) (acc.map (List.map pk)) ∧
      ∀ rs, L.foldl (stepN u l k) acc = some rs → ∀ r ∈ rs, r.2 < 512 := by
  induction L with
  | nil => intro acc h; exact ⟨rfl, h⟩
  | cons x t ih =>
    intro acc hacc
    rw [List.foldl_cons, List.foldl_cons]
    have hstep : (stepN u l k acc x).map (List.map pk) = stepK u l k (acc.map (List.map pk)) x ∧
        ∀ rs, stepN u l k acc x = some rs → ∀ r ∈ rs, r.2 < 512 := by
      cases acc with
      | none => exact ⟨rfl, fun rs h => by cases h⟩
      | some rs =>
        by_cases hz : evalV l (2 ^ k + x) = 0
        · simp [stepN, stepK, hz]
        · have hlm := lmAdd_pk (hacc rs rfl) (x := qOf u (2 ^ k + x))
            (y := qOf u (evalV l (2 ^ k + x))) (qOf_lt u _)
          simp only [stepN, stepK, Option.bind_some, if_neg hz]
          exact hlm
    obtain ⟨h1, h2⟩ := hstep
    obtain ⟨h3, h4⟩ := ih (stepN u l k acc x) h2
    exact ⟨by rw [h3, h1], h4⟩

private theorem addNew_dep (u : Bool) (imgs : List ℕ) (a k : ℕ) (hlen : imgs.length = k)
    (hk : k < 6) (rowsN : List (ℕ × ℕ)) (hrN : ∀ r ∈ rowsN, r.2 < 512)
    (h : ∃ w < 2 ^ k, a ^^^ evalV imgs w = 0) :
    addNew u (imgs ++ [a]) k rowsN = none := by
  obtain ⟨w, hw, hw0⟩ := h
  have h1 := (foldT u (imgs ++ [a]) k (List.range (2 ^ k)) (some rowsN)
    (fun rs h r hr => by cases h; exact hrN r hr)).1
  rw [fold_dep u (imgs ++ [a]) k (List.range (2 ^ k)) ⟨w, List.mem_range.2 hw, by
    rw [evalV_append hlen hk hw]; exact hw0⟩] at h1
  rw [addNew_eq]
  cases h2 : List.foldl (stepN u (imgs ++ [a]) k) (some rowsN) (List.range (2 ^ k)) with
  | none => rfl
  | some rs => rw [h2] at h1; exact absurd h1 (by simp)

private theorem addNew_indep (u : Bool) (imgs : List ℕ) (a k : ℕ) (hlen : imgs.length = k)
    (hk : k < 6) (himgs : ∀ x ∈ imgs, x < 64) (ha : a < 64)
    (hindep : ∀ w < 2 ^ k, a ^^^ evalV imgs w ≠ 0)
    (rowsN : List (ℕ × ℕ)) (hrN : ∀ r ∈ rowsN, r.2 < 512) (hE : Ech 9 (rowsN.map pk))
    (hZ : ∀ v < 2 ^ k, SpN (rowsN.map pk) (rawv u imgs v)) :
    (addNew u (imgs ++ [a]) k rowsN).map (List.map pk) = genF u imgs k a (rowsN.map pk) k ∧
    (∀ rs, addNew u (imgs ++ [a]) k rowsN = some rs → ∀ r ∈ rs, r.2 < 512) ∧
    GoodD u (imgs ++ [a]) k (rowsN.map pk) k (genF u imgs k a (rowsN.map pk) k) := by
  have hT := foldT u (imgs ++ [a]) k (List.range (2 ^ k)) (some rowsN)
    (fun rs h r hr => by cases h; exact hrN r hr)
  have hD := foldD u imgs a k hlen hk himgs ha hindep (rowsN.map pk) hE hZ k le_rfl
  rw [addNew_eq]
  refine ⟨?_, hT.2, hD.2⟩
  rw [hT.1]
  exact hD.1

private theorem xor_cancel_r (a b : ℕ) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

private def InV (l : List ℕ) (x : ℕ) : Prop := ∃ w < 2 ^ l.length, evalV l w = x

private theorem InV_zero (l : List ℕ) : InV l 0 := ⟨0, Nat.two_pow_pos _, evalV_zeroP l⟩

private theorem InV_xor {l : List ℕ} {x y : ℕ} (hx : InV l x) (hy : InV l y) : InV l (x ^^^ y) := by
  obtain ⟨w, hw, rfl⟩ := hx
  obtain ⟨w', hw', rfl⟩ := hy
  exact ⟨w ^^^ w', Nat.xor_lt_two_pow hw hw', evalV_xorP l w w'⟩

private theorem InV_nil {x : ℕ} : InV [] x ↔ x = 0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : w = 0 := by simpa using hw
    subst this; exact evalV_zeroP _
  · rintro rfl; exact InV_zero _

private theorem InV_append {l : List ℕ} {a x : ℕ} (hk : l.length < 6) :
    InV (l ++ [a]) x ↔ InV l x ∨ InV l (x ^^^ a) := by
  have hlen : (l ++ [a]).length = l.length + 1 := by simp
  have hpow : 2 ^ (l.length + 1) = 2 ^ l.length + 2 ^ l.length := by rw [pow_succ]; omega
  constructor
  · rintro ⟨w, hw, hwx⟩
    rw [hlen, hpow] at hw
    by_cases hlt : w < 2 ^ l.length
    · left
      refine ⟨w, hlt, ?_⟩
      rw [← evalV_append_lt rfl hlt (a := a)]; exact hwx
    · right
      have hw' : w - 2 ^ l.length < 2 ^ l.length := by omega
      have h := evalV_append (a := a) rfl hk hw'
      rw [show 2 ^ l.length + (w - 2 ^ l.length) = w by omega, hwx] at h
      refine ⟨w - 2 ^ l.length, hw', ?_⟩
      rw [h, Nat.xor_comm a, xor_cancel_r]
  · rintro (⟨w, hw, hwx⟩ | ⟨w, hw, hwx⟩)
    · refine ⟨w, by rw [hlen, hpow]; omega, ?_⟩
      rw [evalV_append_lt rfl hw]; exact hwx
    · refine ⟨2 ^ l.length + w, by rw [hlen, hpow]; omega, ?_⟩
      rw [evalV_append rfl hk hw, hwx, Nat.xor_comm x a, ← Nat.xor_assoc, Nat.xor_self,
        Nat.zero_xor]

private theorem InV_mem {l : List ℕ} {j : ℕ} (hj : j < l.length) (h6 : l.length ≤ 6) :
    InV l (l.getD j 0) :=
  ⟨2 ^ j, Nat.pow_lt_pow_right Nat.one_lt_two hj, evalV_two_powP (by omega)⟩

private theorem SpN_nil {x : ℕ} : SpN [] x ↔ x = 0 := by
  constructor
  · intro h
    induction h with
    | zero => rfl
    | mem hx => exact absurd hx List.not_mem_nil
    | xor _ _ ih1 ih2 => rw [ih1, ih2]; rfl
  · rintro rfl; exact SpN.zero

private theorem SpN_cons_iff {r : ℕ} {L : List ℕ} {x : ℕ} :
    SpN (r :: L) x ↔ SpN L x ∨ SpN L (x ^^^ r) := by
  constructor
  · intro h
    induction h with
    | zero => exact Or.inl SpN.zero
    | mem hx =>
      rcases List.mem_cons.1 hx with rfl | hx
      · right; rw [Nat.xor_self]; exact SpN.zero
      · exact Or.inl (SpN.mem hx)
    | xor _ _ ih1 ih2 =>
      rename_i a b _ _
      rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
      · exact Or.inl (SpN.xor h1 h2)
      · right; rw [Nat.xor_assoc]; exact SpN.xor h1 h2
      · right; rw [Nat.xor_right_comm]; exact SpN.xor h1 h2
      · left
        have := SpN.xor h1 h2
        rwa [Nat.xor_right_comm, Nat.xor_assoc, xor_cancel_r] at this
  · rintro (h | h)
    · exact h.mono fun y hy => List.mem_cons_of_mem _ hy
    · have h1 : SpN (r :: L) (x ^^^ r) := h.mono fun y hy => List.mem_cons_of_mem _ hy
      have h2 := SpN.xor h1 (SpN.mem (L := r :: L) List.mem_cons_self)
      rwa [xor_cancel_r] at h2

private theorem SpN_oins {s p : ℕ} {L : List ℕ} {x : ℕ} : SpN (oins s p L) x ↔ SpN (p :: L) x := by
  have hm : ∀ y, y ∈ oins s p L ↔ y ∈ p :: L := fun y => by
    unfold oins
    rw [List.mem_orderedInsert, List.mem_cons]
  exact ⟨fun h => h.mono fun y hy => (hm y).1 hy, fun h => h.mono fun y hy => (hm y).2 hy⟩

private theorem red_zero_iff {ib imgs : List ℕ} (hE : Ech 0 ib) (hI : ∀ x, SpN ib x ↔ InV imgs x)
    (a : ℕ) : red 0 ib a = 0 ↔ InV imgs a := by
  constructor
  · intro h
    obtain ⟨w, hw, hwa⟩ := red_sp 0 ib a
    rw [h] at hwa
    have : a = w := by
      have := congrArg (· ^^^ w) hwa
      simp only [Nat.zero_xor, xor_cancel_r] at this
      exact this.symm
    rw [this]; exact (hI w).1 hw
  · intro h
    exact red_of_sp 0 ib hE ((hI a).2 h)

private theorem qK_eq : ∀ u : Bool, ∀ v < 64, qK (if u then 1 else 0) v = qOf u v := by
  decide +kernel

private theorem betaK_eq : ∀ u : Bool, ∀ v < 64, ∀ w < 64,
    betaK (if u then 1 else 0) v w = betaOf u v w := by
  decide +kernel

private theorem fld6_eq (P j : ℕ) : fld6 P j = P / 64 ^ j % 64 := by
  have h : fld6 P j = (P >>> (6 * j)) &&& 63 := rfl
  have h63 : (63 : ℕ) = 2 ^ 6 - 1 := rfl
  rw [h, h63, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

private theorem filterK_aux (f : ℕ → Bool) (n : ℕ) : ∀ acc : List ℕ,
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun v ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons v acc) (f v)))
      n acc = (List.range n).filter f ++ acc := by
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    show Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun v ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons v acc) (f v)))
      n (Bool.rec (motive := fun _ => List Nat) acc (List.cons n acc) (f n)) = _
    rw [ih, List.range_succ, List.filter_append]
    cases h : f n <;> simp [h]

private theorem fibOf_getD (u : Bool) {y : ℕ} (hy : y < 512) :
    (fibOf u).getD y [] = (List.range 64).filter fun v => qOf u v == y := by
  have key : ∀ b, (fibTab b).getD y [] = (List.range 64).filter fun v => qOf b v == y := by
    intro b
    unfold fibTab
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_range hy]
    rfl
  unfold fibOf fibU fibL
  cases u <;> exact key _

private theorem cands_lt (u : Bool) {k : ℕ} (rowsN : List (ℕ × ℕ)) (hr : ∀ r ∈ rowsN, r.2 < 512) :
    ∀ t ∈ cands u k rowsN, t < 64 := by
  intro t ht
  unfold cands at ht
  split at ht
  · have hy := (lmRed_pk rowsN hr (qOf u (2 ^ k), 0) (by simp)).2
    exact ((mem_fibOf hy).1 ht).1
  · exact List.mem_range.1 ht

private theorem candsK_letL (y : ℕ) (k : ℕ → List ℕ) : candsK.letL y k = k y := by
  cases y <;> rfl

private theorem candsK_eq (u : Bool) {k : ℕ} (hk : k < 6) (rowsN : List (ℕ × ℕ))
    (hr : ∀ r ∈ rowsN, r.2 < 512) :
    candsK (if u then 1 else 0) k (rowsN.map pk) = cands u k rowsN := by
  have hk64 : 2 ^ k < 64 :=
    calc 2 ^ k < 2 ^ 6 := Nat.pow_lt_pow_right Nat.one_lt_two hk
      _ = 64 := rfl
  have h0 := lmRed_pk rowsN hr (qOf u (2 ^ k), 0) (by simp)
  have hq : qK (if u then 1 else 0) (Nat.pow 2 k) = qOf u (2 ^ k) := qK_eq u _ hk64
  have : candsK (if u then 1 else 0) k (rowsN.map pk) = candsK.letL
      (lmRedK (rowsN.map pk) (Nat.mul (qK (if u then 1 else 0) (Nat.pow 2 k)) 512)) fun p =>
        Bool.rec (motive := fun _ => List Nat) (candsK.rangeK 64)
          (candsK.filterK 64 fun v => Nat.beq (qK (if u then 1 else 0) v) (Nat.land p 511))
          (Nat.beq (Nat.shiftRight p 9) 0) := rfl
  rw [this, candsK_letL, hq, lmRedK_eq]
  have hpk : Nat.mul (qOf u (2 ^ k)) 512 = pk (qOf u (2 ^ k), 0) := by
    have : pk (qOf u (2 ^ k), 0) = qOf u (2 ^ k) * 512 := by unfold pk; exact Nat.add_zero _
    rw [this]; rfl
  rw [hpk, h0.1]
  unfold cands
  generalize lmRed rowsN (qOf u (2 ^ k), 0) = p at h0
  have hp2 : p.2 < 512 := h0.2
  have hs : Nat.shiftRight (pk p) 9 = p.1 := pk_shift hp2
  have hl : Nat.land (pk p) 511 = p.2 := pk_land hp2
  show Bool.rec (motive := fun _ => List Nat) _ _ (Nat.beq (Nat.shiftRight (pk p) 9) 0) = _
  rw [hs]
  by_cases h1 : p.1 = 0
  · have hb : Nat.beq p.1 0 = true := Nat.beq_eq ▸ h1
    rw [hb, if_pos h1]
    show candsK.filterK 64 _ = _
    unfold candsK.filterK
    rw [filterK_aux _ 64 [], List.append_nil, fibOf_getD u hp2, hl]
    refine List.filter_congr fun v hv => ?_
    have hv64 : v < 64 := List.mem_range.1 hv
    rw [qK_eq u v hv64]
    exact Bool.eq_iff_iff.2 (by simp [Nat.beq_eq])
  · have hb : Nat.beq p.1 0 = false := by
      cases h : Nat.beq p.1 0
      · rfl
      · exact absurd (Nat.beq_eq ▸ h) h1
    rw [hb, if_neg h1]
    show candsK.rangeK 64 = _
    unfold candsK.rangeK candsK.filterK
    rw [filterK_aux (fun _ => true) 64 [], List.append_nil]
    exact List.filter_true _

private theorem pairsK_eq (u : Bool) (imgs : List ℕ) (a P k : ℕ) (hlen : imgs.length = k)
    (hk : k < 6) (himgs : ∀ x ∈ imgs, x < 64) (ha : a < 64)
    (hP : ∀ j < k, fld6 P j = imgs.getD j 0) (rows : List ℕ) :
    pairsK (if u then 1 else 0) P k a rows = genF u imgs k a rows k := by
  have hpow : ∀ j, j ≤ k → 2 ^ j < 64 := fun j hj =>
    calc 2 ^ j < 2 ^ 6 := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
      _ = 64 := rfl
  have hgetD : ∀ j, j < k → imgs.getD j 0 < 64 := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact himgs _ (List.getElem_mem _)
  unfold pairsK
  have key : ∀ j, j ≤ k → Nat.rec (motive := fun _ => Option (List Nat))
      (lmAddK rows (qK (if u then 1 else 0) (Nat.pow 2 k)) (qK (if u then 1 else 0) a))
      (fun j acc => Option.rec (motive := fun _ => Option (List Nat)) none
        (fun rs => lmAddK rs (betaK (if u then 1 else 0) (Nat.pow 2 k) (Nat.pow 2 j))
          (betaK (if u then 1 else 0) a (fld6 P j))) acc) j = genF u imgs k a rows j := by
    intro j
    induction j with
    | zero =>
      intro _
      show lmAddK rows (qK (if u then 1 else 0) (Nat.pow 2 k)) (qK (if u then 1 else 0) a) =
        lmAddK rows (qOf u (2 ^ k)) (qOf u a)
      have e1 : qK (if u then 1 else 0) (Nat.pow 2 k) = qOf u (2 ^ k) :=
        qK_eq u _ (hpow k le_rfl)
      rw [e1, qK_eq u _ ha]
    | succ j ih =>
      intro hj
      show Option.rec (motive := fun _ => Option (List Nat)) none
        (fun rs => lmAddK rs (betaK (if u then 1 else 0) (Nat.pow 2 k) (Nat.pow 2 j))
          (betaK (if u then 1 else 0) a (fld6 P j))) _ = (genF u imgs k a rows j).bind _
      rw [ih (by omega)]
      cases genF u imgs k a rows j with
      | none => rfl
      | some rs =>
        show lmAddK rs _ _ = lmAddK rs _ _
        have e2 : betaK (if u then 1 else 0) (Nat.pow 2 k) (Nat.pow 2 j) =
            betaOf u (2 ^ k) (2 ^ j) := betaK_eq u _ (hpow k le_rfl) _ (hpow j (by omega))
        rw [e2, hP j (by omega), betaK_eq u _ ha _ (hgetD j (by omega))]
  exact key k le_rfl

private theorem step2K_letS (y : ℕ) (k : ℕ → List (ℕ × List ℕ × List ℕ)) :
    step2K.letS y k = k y := by
  cases y <;> rfl

private noncomputable def Kopt (u k P : ℕ) (rows ib : List ℕ) (a : ℕ) :
    Option (ℕ × List ℕ × List ℕ) :=
  if redV ib a = 0 then none
  else (pairsK u P k a rows).map fun rs =>
    (Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)), rs, insV (redV ib a) ib)

private theorem step2K_eq (u k P : ℕ) (rows ib : List ℕ) :
    step2K u k (P, rows, ib) = (candsK u k rows).flatMap fun a => (Kopt u k P rows ib a).toList := by
  have key : ∀ C : List ℕ, List.rec (motive := fun _ => List (ℕ × List ℕ × List ℕ)) List.nil
      (fun a _ ih => step2K.letS (redV ib a) fun ra =>
        Bool.rec (motive := fun _ => List (ℕ × List ℕ × List ℕ))
          (Option.rec (motive := fun _ => List (ℕ × List ℕ × List ℕ)) ih
            (fun rs => List.cons (Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)), rs, insV ra ib) ih)
            (pairsK u P k a rows)) ih (Nat.beq ra 0)) C =
      C.flatMap fun a => (Kopt u k P rows ib a).toList := by
    intro C
    induction C with
    | nil => rfl
    | cons a t ih =>
      rw [List.flatMap_cons, ← ih]
      show step2K.letS (redV ib a) _ = _
      rw [step2K_letS]
      unfold Kopt
      cases hb : Nat.beq (redV ib a) 0
      · have hne : ¬ redV ib a = 0 := fun h => by
          rw [h] at hb; exact absurd hb (by decide)
        rw [if_neg hne]
        cases pairsK u P k a rows <;> rfl
      · have h0 : redV ib a = 0 := Nat.beq_eq ▸ hb
        rw [if_pos h0]
        rfl
  exact key _

private theorem oqStep_eq (u : Bool) (k : ℕ) (imgs : List ℕ) (rowsN : List (ℕ × ℕ)) :
    oqStep u k (imgs, rowsN) = (cands u k rowsN).flatMap fun t =>
      ((addNew u (imgs ++ [t]) k rowsN).map fun rs => (imgs ++ [t], rs)).toList := by
  unfold oqStep
  rw [List.filterMap_eq_flatMap_toList]

private theorem fld6_add_lt {P a k j : ℕ} (hj : j < k) :
    fld6 (P + a * 64 ^ k) j = fld6 P j := by
  rw [fld6_eq, fld6_eq]
  obtain ⟨m, rfl⟩ : ∃ m, k = j + 1 + m := ⟨k - j - 1, by omega⟩
  have h : 64 ^ (j + 1 + m) = 64 ^ j * (64 * 64 ^ m) := by
    rw [Nat.pow_add, Nat.pow_succ, Nat.mul_assoc]
  have hpos : 0 < 64 ^ j := Nat.pow_pos (by decide)
  rw [h, Nat.mul_left_comm a (64 ^ j), Nat.add_mul_div_left _ _ hpos,
    show a * (64 * 64 ^ m) = 64 * (a * 64 ^ m) from Nat.mul_left_comm _ _ _,
    Nat.add_mul_mod_self_left]

private theorem fld6_add_eq {P a k : ℕ} (hP : P < 64 ^ k) (ha : a < 64) :
    fld6 (P + a * 64 ^ k) k = a := by
  rw [fld6_eq]
  have hpos : 0 < 64 ^ k := Nat.pow_pos (by decide)
  rw [Nat.mul_comm a, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hP, Nat.zero_add,
    Nat.mod_eq_of_lt ha]

private theorem shl_eq (P a k : ℕ) :
    Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)) = P + a * 64 ^ k := by
  show P + (a <<< (6 * k)) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  rfl

private def Rel (u : Bool) (k : ℕ) (st : ℕ × List ℕ × List ℕ) (stN : List ℕ × List (ℕ × ℕ)) :
    Prop :=
  stN.1.length = k ∧ k ≤ 6 ∧ (∀ x ∈ stN.1, x < 64) ∧ st.1 < 64 ^ k ∧
    (∀ j < k, fld6 st.1 j = stN.1.getD j 0) ∧
    st.2.1 = stN.2.map pk ∧ (∀ r ∈ stN.2, r.2 < 512) ∧ Ech 9 st.2.1 ∧
    (∀ v < 2 ^ k, SpN st.2.1 (rawv u stN.1 v)) ∧
    Ech 0 st.2.2 ∧ (∀ x, SpN st.2.2 x ↔ InV stN.1 x)

private theorem rel_one (u : Bool) {k P : ℕ} {rows ib imgs : List ℕ} {rowsN : List (ℕ × ℕ)}
    (hk : k < 6) (hR : Rel u k (P, rows, ib) (imgs, rowsN)) {a : ℕ} (ha : a < 64) :
    (Kopt (if u then 1 else 0) k P rows ib a = none ∧
      (addNew u (imgs ++ [a]) k rowsN).map (fun rs => (imgs ++ [a], rs)) = none) ∨
    ∃ stK stN, Kopt (if u then 1 else 0) k P rows ib a = some stK ∧
      (addNew u (imgs ++ [a]) k rowsN).map (fun rs => (imgs ++ [a], rs)) = some stN ∧
      Rel u (k + 1) stK stN := by
  obtain ⟨hlen, -, himgs, hPlt, hPf, hrows, hrN, hE9, hZ, hE0, hIb⟩ := hR
  simp only at hlen himgs hPlt hPf hrows hrN hE9 hZ hE0 hIb
  subst hrows
  by_cases hz : red 0 ib a = 0
  · left
    have hKz : Kopt (if u then 1 else 0) k P (rowsN.map pk) ib a = none := by
      unfold Kopt; rw [if_pos (by rw [redV_eq]; exact hz)]
    refine ⟨hKz, ?_⟩
    obtain ⟨w, hw, hwa⟩ := (red_zero_iff hE0 hIb a).1 hz
    rw [hlen] at hw
    rw [addNew_dep u imgs a k hlen hk rowsN hrN ⟨w, hw, by rw [← hwa, Nat.xor_self]⟩]
    rfl
  · have hindep : ∀ w < 2 ^ k, a ^^^ evalV imgs w ≠ 0 := by
      intro w hw h0
      apply hz
      refine (red_zero_iff hE0 hIb a).2 ⟨w, by rw [hlen]; exact hw, ?_⟩
      have := congrArg (· ^^^ evalV imgs w) h0
      simp only [Nat.zero_xor, xor_cancel_r] at this
      exact this.symm
    obtain ⟨hmap, hbd, hgood⟩ := addNew_indep u imgs a k hlen hk himgs ha hindep rowsN hrN hE9 hZ
    have hpair := pairsK_eq u imgs a P k hlen hk himgs ha hPf (rowsN.map pk)
    rw [← hpair] at hmap hgood
    have hKnz : Kopt (if u then 1 else 0) k P (rowsN.map pk) ib a =
        (pairsK (if u then 1 else 0) P k a (rowsN.map pk)).map fun rs =>
          (Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)), rs, insV (redV ib a) ib) := by
      unfold Kopt; rw [if_neg (by rw [redV_eq]; exact hz)]
    cases hN : addNew u (imgs ++ [a]) k rowsN with
    | none =>
      left
      rw [hN] at hmap
      refine ⟨?_, rfl⟩
      rw [hKnz, ← hmap]; rfl
    | some rsN =>
      right
      rw [hN] at hmap
      simp only [Option.map_some] at hmap
      refine ⟨(Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)), rsN.map pk, insV (redV ib a) ib),
        (imgs ++ [a], rsN), ?_, rfl, ?_⟩
      · rw [hKnz, ← hmap]; rfl
      · obtain ⟨hE', hsub, hZ'⟩ := hgood _ hmap.symm
        have h64 : 0 < 64 ^ k := Nat.pow_pos (by decide)
        have hak : a * 64 ^ k ≤ 63 * 64 ^ k := Nat.mul_le_mul_right _ (by omega)
        have hsh := shl_eq P a k
        have hpowS : 64 ^ (k + 1) = 64 * 64 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
        refine ⟨by simp [hlen], by omega, ?_, ?_, ?_, rfl, hbd rsN hN, hE', ?_, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact himgs x hx
          · rw [List.mem_singleton.1 hx]; exact ha
        · show Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)) < 64 ^ (k + 1)
          rw [hsh, hpowS]; omega
        · intro j hj
          show fld6 (Nat.add P (Nat.shiftLeft a (Nat.mul 6 k))) j = _
          rw [hsh]
          by_cases hjk : j < k
          · rw [fld6_add_lt hjk, hPf j hjk, List.getD_append _ _ _ _ (by omega)]
          · have : j = k := by omega
            subst this
            rw [fld6_add_eq hPlt ha, List.getD_append_right _ _ _ _ (by omega)]
            simp [hlen]
        · intro v hv
          by_cases hvk : v < 2 ^ k
          · show SpN (rsN.map pk) (rawv u (imgs ++ [a]) v)
            rw [rawv_append_lt hlen hvk]
            exact (hZ v hvk).mono hsub
          · have hpw : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
            have := hZ' (v - 2 ^ k) (by omega)
            rwa [Nat.add_sub_cancel' (by omega)] at this
        · show Ech 0 (insV (redV ib a) ib)
          rw [insV_eq, redV_eq]
          refine Ech_oins 0 _ hE0 ?_ (red_clears 0 ib hE0 a)
          simpa using hz
        · intro x
          show SpN (insV (redV ib a) ib) x ↔ InV (imgs ++ [a]) x
          rw [insV_eq, redV_eq, SpN_oins, SpN_cons_iff, hIb, hIb, InV_append (by omega)]
          obtain ⟨w₀, hw₀, hra⟩ := red_sp 0 ib a
          have hw₀' : InV imgs w₀ := (hIb w₀).1 hw₀
          rw [hra]
          have hxe : x ^^^ (a ^^^ w₀) = (x ^^^ a) ^^^ w₀ := by rw [Nat.xor_assoc]
          rw [hxe]
          constructor
          · rintro (h | h)
            · exact Or.inl h
            · right
              have := InV_xor h hw₀'
              rwa [xor_cancel_r] at this
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (InV_xor h hw₀')

private theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {m₁ m₂ : List β}
    (h1 : List.Forall₂ R l₁ m₁) (h2 : List.Forall₂ R l₂ m₂) :
    List.Forall₂ R (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h1 with
  | nil => exact h2
  | cons hab _ ih => exact List.Forall₂.cons hab ih

private theorem forall₂_flatMap {α β γ : Type} {R : β → γ → Prop} {f : α → List β}
    {g : α → List γ} {C : List α} (h : ∀ a ∈ C, List.Forall₂ R (f a) (g a)) :
    List.Forall₂ R (C.flatMap f) (C.flatMap g) := by
  induction C with
  | nil => exact List.Forall₂.nil
  | cons a t ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact forall₂_append (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem forall₂_flatMap' {α α' β γ : Type} {S : α → α' → Prop} {R : β → γ → Prop}
    {f : α → List β} {g : α' → List γ} {L : List α} {LN : List α'}
    (hL : List.Forall₂ S L LN) (h : ∀ x y, S x y → List.Forall₂ R (f x) (g y)) :
    List.Forall₂ R (L.flatMap f) (LN.flatMap g) := by
  induction hL with
  | nil => exact List.Forall₂.nil
  | cons hxy _ ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact forall₂_append (h _ _ hxy) ih

private theorem level_rel (u : Bool) {k : ℕ} (hk : k < 6) {st : ℕ × List ℕ × List ℕ}
    {stN : List ℕ × List (ℕ × ℕ)} (hR : Rel u k st stN) :
    List.Forall₂ (Rel u (k + 1)) (step2K (if u then 1 else 0) k st) (oqStep u k stN) := by
  obtain ⟨P, rows, ib⟩ := st
  obtain ⟨imgs, rowsN⟩ := stN
  have hrN := hR.2.2.2.2.2.2.1
  have hrows : rows = rowsN.map pk := hR.2.2.2.2.2.1
  subst hrows
  rw [step2K_eq, oqStep_eq, candsK_eq u hk rowsN hrN]
  refine forall₂_flatMap fun a ha => ?_
  have ha64 := cands_lt u rowsN hrN a ha
  rcases rel_one u hk hR ha64 with ⟨h1, h2⟩ | ⟨stK, stN, h1, h2, h3⟩
  · rw [h1, h2]; exact List.Forall₂.nil
  · rw [h1, h2]; exact List.Forall₂.cons h3 List.Forall₂.nil

private theorem appK_eqP {α : Type} (l₁ l₂ : List α) : appK l₁ l₂ = l₁ ++ l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a t ih =>
    show List.cons a (appK t l₂) = _
    rw [ih]; rfl

private theorem level2K_eq (u k : ℕ) (L : List (ℕ × List ℕ × List ℕ)) :
    level2K u k L = L.flatMap (step2K u k) := by
  induction L with
  | nil => rfl
  | cons st t ih =>
    show appK (step2K u k st) (level2K u k t) = _
    rw [appK_eqP, ih, List.flatMap_cons]

private theorem fstsK_eq (L : List (ℕ × List ℕ × List ℕ)) : fstsK L = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons st t ih =>
    show List.cons st.1 (fstsK t) = _
    rw [ih]; rfl

private noncomputable def lvl (u : ℕ) : ℕ → List (ℕ × List ℕ × List ℕ) → List (ℕ × List ℕ × List ℕ)
  | 0, L => L
  | m + 1, L => level2K u (m + 1) (lvl u m L)

private theorem levels2K_one (u : ℕ) (L : List (ℕ × List ℕ × List ℕ)) :
    levels2K u 1 L = lvl u 5 L := rfl

private theorem oqStatesFrom_succ (u : Bool) (t m : ℕ) :
    oqStatesFrom u t (m + 1) = (oqStatesFrom u t m).flatMap (oqStep u (m + 1)) := by
  unfold oqStatesFrom
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem addNew_one (u : Bool) (t : ℕ) :
    addNew u [t] 0 [] = if t = 0 then none else lmAdd [] (qOf u 1) (qOf u t) := by
  have h1 : evalV [t] (2 ^ 0 + 0) = t := by
    have := evalV_two_powP (l := [t]) (j := 0) (by omega)
    rw [Nat.add_zero]; exact this
  have hr : List.range (2 ^ 0) = [0] := rfl
  unfold addNew
  rw [hr, List.foldl_cons, List.foldl_nil]
  show (some []).bind _ = _
  simp only [Option.bind_some, h1]
  by_cases ht : t = 0
  · simp [ht]
  · simp [ht]

private theorem rel_init_one (u : Bool) {t : ℕ} (ht0 : t ≠ 0) (ht : t < 64) {x y : ℕ}
    (hx : x = qOf u 1) (hy : y = qOf u t) (hx0 : x ≠ 0) :
    Rel u 1 (t, [x * 512 + y], [t]) ([t], [(x, y)]) := by
  have hy512 : y < 512 := hy ▸ qOf_lt u t
  have hpk : pk (x, y) = x * 512 + y := rfl
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz; rw [List.mem_singleton.1 hz]; exact ht
  · rw [pow_one]; exact ht
  · intro j hj
    have : j = 0 := by omega
    subst this
    rw [fld6_eq]
    show t / 64 ^ 0 % 64 = t
    rw [pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt ht
  · rfl
  · intro r hr; rw [List.mem_singleton.1 hr]; exact hy512
  · refine ⟨?_, List.pairwise_singleton _ _⟩
    intro r hr
    rw [List.mem_singleton.1 hr]
    have := pk_shift (p := (x, y)) hy512
    rw [hpk] at this
    rw [this]; exact hx0
  · intro v hv
    have : v = 0 ∨ v = 1 := by omega
    rcases this with rfl | rfl
    · rw [rawv_zero]; exact SpN.zero
    · apply SpN.mem
      have h1 : evalV [t] 1 = t := by
        have := evalV_two_powP (l := [t]) (j := 0) (by omega)
        exact this
      show rawv u [t] 1 ∈ [x * 512 + y]
      unfold rawv
      rw [h1, ← hx, ← hy]
      show x * 512 + y ∈ [x * 512 + y]
      exact List.mem_singleton_self _
  · exact ⟨fun r hr => by rw [List.mem_singleton.1 hr]; exact ht0, List.pairwise_singleton _ _⟩
  · intro z
    rw [SpN_cons_iff, SpN_nil, SpN_nil]
    have := @InV_append [] t z (by simp)
    show _ ↔ InV ([] ++ [t]) z
    rw [this, InV_nil, InV_nil]

private theorem rel_init (u : Bool) {t : ℕ} (ht : t < 64) :
    List.Forall₂ (Rel u 1) (initK (if u then 1 else 0) t) (oqStatesFrom u t 0) := by
  have hN : oqStatesFrom u t 0 = ((addNew u [t] 0 []).map fun rs => ([t], rs)).toList := rfl
  rw [hN, addNew_one]
  by_cases ht0 : t = 0
  · subst ht0
    have : initK (if u then 1 else 0) 0 = [] := rfl
    rw [this]
    simp
  · have hK : initK (if u then 1 else 0) t =
        Option.rec (motive := fun _ => List (ℕ × List ℕ × List ℕ)) List.nil
          (fun rs => List.cons (t, rs, List.cons t List.nil) List.nil)
          (lmAddK List.nil (qK (if u then 1 else 0) 1) (qK (if u then 1 else 0) t)) := by
      have : Nat.beq t 0 = false := by
        cases h : Nat.beq t 0
        · rfl
        · exact absurd (Nat.beq_eq ▸ h) ht0
      unfold initK
      rw [this]
    rw [hK, qK_eq u 1 (by omega), qK_eq u t ht, lmAddK_eq]
    have hred : red 9 [] (qOf u 1 * 512 + qOf u t) = qOf u 1 * 512 + qOf u t := rfl
    rw [hred, if_neg ht0]
    have hy512 : qOf u t < 512 := qOf_lt u t
    by_cases hx : qOf u 1 = 0
    · by_cases hy : qOf u t = 0
      · have e1 : addP [] (qOf u 1 * 512 + qOf u t) = some [] := by
          rw [hx, hy]; rfl
        have e2 : lmAdd [] (qOf u 1) (qOf u t) = some [] := by
          rw [hx, hy]; rfl
        rw [e1, e2]
        refine List.Forall₂.cons ?_ List.Forall₂.nil
        refine ⟨rfl, by omega, ?_, ?_, ?_, rfl, ?_, ⟨by simp, List.Pairwise.nil⟩, ?_, ?_, ?_⟩
        · intro z hz; rw [List.mem_singleton.1 hz]; exact ht
        · rw [pow_one]; exact ht
        · intro j hj
          have : j = 0 := by omega
          subst this
          rw [fld6_eq]
          show t / 64 ^ 0 % 64 = t
          rw [pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt ht
        · intro r hr; exact absurd hr List.not_mem_nil
        · intro v hv
          have : v = 0 ∨ v = 1 := by omega
          rcases this with rfl | rfl
          · rw [rawv_zero]; exact SpN.zero
          · have h1 : evalV [t] 1 = t := evalV_two_powP (l := [t]) (j := 0) (by omega)
            have : rawv u [t] 1 = 0 := by
              unfold rawv
              rw [h1]
              show qOf u 1 * 512 + qOf u t = 0
              rw [hx, hy]
            show SpN [] (rawv u [t] 1)
            rw [this]; exact SpN.zero
        · exact ⟨fun r hr => by rw [List.mem_singleton.1 hr]; exact ht0, List.pairwise_singleton _ _⟩
        · intro z
          rw [SpN_cons_iff, SpN_nil, SpN_nil]
          have := @InV_append [] t z (by simp)
          show _ ↔ InV ([] ++ [t]) z
          rw [this, InV_nil, InV_nil]
      · have e1 : addP [] (qOf u 1 * 512 + qOf u t) = none := by
          unfold addP
          have h1 : (qOf u 1 * 512 + qOf u t) >>> 9 = 0 := by
            rw [Nat.shiftRight_eq_div_pow, hx]
            show (0 * 512 + qOf u t) / 2 ^ 9 = 0
            have : (2 : ℕ) ^ 9 = 512 := rfl
            rw [this]; omega
          have h2 : (qOf u 1 * 512 + qOf u t) &&& 511 ≠ 0 := by
            have h511 : (511 : ℕ) = 2 ^ 9 - 1 := rfl
            rw [h511, Nat.and_two_pow_sub_one_eq_mod, hx]
            show (0 * 512 + qOf u t) % 2 ^ 9 ≠ 0
            have : (2 : ℕ) ^ 9 = 512 := rfl
            rw [this]; omega
          rw [if_pos h1, if_neg h2]
        have e2 : lmAdd [] (qOf u 1) (qOf u t) = none := by
          rw [hx]
          show (if ((0, qOf u t) : ℕ × ℕ).1 = 0 then
            (if ((0, qOf u t) : ℕ × ℕ).2 = 0 then some [] else none) else _) = none
          simp [hy]
        rw [e1, e2]
        exact List.Forall₂.nil
    · have e1 : addP [] (qOf u 1 * 512 + qOf u t) = some [qOf u 1 * 512 + qOf u t] := by
        unfold addP
        have h1 : ((qOf u 1 * 512 + qOf u t) >>> 9) ≠ 0 := by
          have := pk_shift (p := (qOf u 1, qOf u t)) hy512
          exact fun h => hx (this.symm.trans h)
        rw [if_neg h1]
        simp [oins]
      have e2 : lmAdd [] (qOf u 1) (qOf u t) = some [(qOf u 1, qOf u t)] := by
        show (if ((qOf u 1, qOf u t) : ℕ × ℕ).1 = 0 then _ else _) = _
        simp only [hx, if_false]
        simp [lmRed]
      rw [e1, e2]
      exact List.Forall₂.cons (rel_init_one u ht0 ht rfl rfl hx) List.Forall₂.nil

private theorem rel_chain (u : Bool) {t : ℕ} (ht : t < 64) :
    ∀ m, m ≤ 5 → List.Forall₂ (Rel u (m + 1))
      (lvl (if u then 1 else 0) m (initK (if u then 1 else 0) t)) (oqStatesFrom u t m) := by
  intro m
  induction m with
  | zero => intro _; exact rel_init u ht
  | succ m ih =>
    intro hm
    have h := ih (by omega)
    have e1 : lvl (if u then 1 else 0) (m + 1) (initK (if u then 1 else 0) t) =
        (lvl (if u then 1 else 0) m (initK (if u then 1 else 0) t)).flatMap
          (step2K (if u then 1 else 0) (m + 1)) := level2K_eq _ _ _
    rw [e1, oqStatesFrom_succ]
    exact forall₂_flatMap' h fun x y hxy => level_rel u (k := m + 1) (by omega) hxy

private theorem unpack6_of_rel (u : Bool) {st : ℕ × List ℕ × List ℕ} {stN : List ℕ × List (ℕ × ℕ)}
    (h : Rel u 6 st stN) : unpack6 st.1 = stN.1 := by
  obtain ⟨hlen, -, -, -, hf, -⟩ := h
  apply List.ext_getElem
  · simp [unpack6, hlen]
  · intro i h1 h2
    have hi : i < 6 := by simpa [unpack6] using h1
    have := hf i hi
    rw [fld6_eq, List.getD_eq_getElem _ _ h2] at this
    simpa [unpack6] using this

private theorem fsts_rel (u : Bool) {L : List (ℕ × List ℕ × List ℕ)}
    {LN : List (List ℕ × List (ℕ × ℕ))} (h : List.Forall₂ (Rel u 6) L LN) :
    (fstsK L).map unpack6 = LN.map Prod.fst := by
  induction h with
  | nil => rfl
  | @cons a b _ _ hab _ ih =>
    show List.cons (unpack6 a.1) ((fstsK _).map unpack6) = _
    rw [ih, unpack6_of_rel u hab]
    rfl

theorem search2K_sound' (u : Bool) {t : ℕ} (ht : t < 64) :
    (search2K (if u then 1 else 0) t).map unpack6 = oqFrom u t := by
  have h := rel_chain u ht 5 le_rfl
  exact fsts_rel u h

end CFSG.KC.Misc.Oq

end
