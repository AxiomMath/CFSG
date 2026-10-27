module

public import Certificates.Data.Kernel.J4Q.MatChk
public import CFSG.Sporadic.J4.Setup
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Data.Fintype.Card

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.KC.Loop

@[expose] noncomputable def encR (X : Array V2) : Nat :=
  (List.range 112).foldr (fun i acc => Nat.lor (Nat.shiftLeft (v2N (X.getD i V2.zero)) (128 * i)) acc) 0

@[expose] def WfA (X : Array V2) : Prop := X.size = 112 ∧ X.all V2.wf = true

@[expose] def Consts (c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat) : Prop :=
  constsOK c rm one pad t0 t1 t2 t3 t4 t5 t6 = true

private theorem lt64 (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

private theorem v2N_testBit (v : V2) (k : Nat) :
    (v2N v).testBit k = if k < 64 then v.lo.toNat.testBit k else v.hi.toNat.testBit (k - 64) := by
  change (v.lo.toNat ||| (v.hi.toNat <<< 64)).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < 64
  · have h1 : ¬ k ≥ 64 := by omega
    simp [hk, h1]
  · have h1 : k ≥ 64 := by omega
    have h2 : v.lo.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64 v.lo) (Nat.pow_le_pow_right (by omega) h1))
    simp [hk, h1, h2]

private theorem shl_one_toNat (j : Nat) :
    ((1 : UInt64) <<< UInt64.ofNat (j % 64)).toNat = 2 ^ (j % 64) := by
  have hj : j % 64 < 64 := Nat.mod_lt _ (by omega)
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_ofNat']
  have e1 : j % 64 % 2 ^ 64 % 64 = j % 64 := by
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj (by decide)), Nat.mod_eq_of_lt hj]
  rw [e1, UInt64.toNat_one, Nat.one_shiftLeft]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hj)

private theorem setBit_bits (v : V2) {j : Nat} (hj : j < 112) (k : Nat) :
    (v2N (v.setBit j)).testBit k = ((v2N v).testBit k || decide (k = j)) := by
  unfold V2.setBit
  by_cases h : j / 64 = 0
  · simp only [h, ↓reduceIte]
    rw [v2N_testBit, v2N_testBit]
    have hj' : j < 64 := by omega
    have hm : j % 64 = j := Nat.mod_eq_of_lt hj'
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNat, hm, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        simp
      · have e' : ¬ j = k := fun h => e h.symm
        simp [e, e']
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
  · simp only [h, ↓reduceIte]
    rw [v2N_testBit, v2N_testBit]
    have hj' : 64 ≤ j := by omega
    by_cases hk : k < 64
    · simp only [hk, ↓reduceIte]
      have e : ¬ k = j := by omega
      simp [e]
    · simp only [hk, ↓reduceIte]
      rw [UInt64.toNat_or, shl_one_toNat, Nat.testBit_or, Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        have : k % 64 = k - 64 := by omega
        simp [this]
      · have e' : ¬ j % 64 = k - 64 := by omega
        simp [e, e']

private theorem ofFn_bits (f : Nat → Bool) (k : Nat) :
    (v2N (V2.ofFn f)).testBit k = (decide (k < 112) && f k) := by
  have key : ∀ m ≤ 112, (v2N ((List.range m).foldl
      (fun v j => if f j then v.setBit j else v) V2.zero)).testBit k = (decide (k < m) && f k) := by
    intro m
    induction m with
    | zero =>
      intro _
      have : v2N V2.zero = 0 := rfl
      simp [this]
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      by_cases hf : f m
      · simp only [hf, ↓reduceIte]
        rw [setBit_bits _ (by omega), ih (by omega)]
        by_cases e : k = m
        · subst e
          simp [hf]
        · have h1 : (k < m + 1) ↔ k < m := by omega
          simp [e, h1]
      · have hf' : f m = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, ↓reduceIte]
        rw [ih (by omega)]
        by_cases e : k = m
        · subst e
          simp [hf]
        · have h1 : (k < m + 1) ↔ k < m := by omega
          simp [h1]
  exact key 112 (Nat.le_refl _)

theorem wf_of_bits {v : V2} (h : ∀ k, 112 ≤ k → (v2N v).testBit k = false) :
    v.wf = true := by
  have hhi : v.hi.toNat < 2 ^ 48 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    have := h (i + 64) (by omega)
    rw [v2N_testBit] at this
    have h1 : ¬ i + 64 < 64 := by omega
    simp only [h1, ↓reduceIte, Nat.add_sub_cancel] at this
    exact this
  unfold V2.wf
  have e : v.hi >>> 48 = 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, UInt64.toNat_zero]
    have : (48 : UInt64).toNat % 64 = 48 := rfl
    rw [this]
    exact Nat.shiftRight_eq_zero _ _ hhi
  rw [e]
  rfl

private theorem wf_ofFn (f : Nat → Bool) : (V2.ofFn f).wf = true :=
  wf_of_bits (fun k hk => by
    rw [ofFn_bits]
    have : ¬ k < 112 := by omega
    simp [this])

private theorem wf_iff (v : V2) : v.wf = true ↔ v.hi.toNat < 2 ^ 48 := by
  unfold V2.wf
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, UInt64.toNat_zero]
  have : (48 : UInt64).toNat % 64 = 48 := rfl
  rw [this, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 48))
    · exact h
  · exact Or.inr

private theorem wf_xor {a b : V2} (ha : a.wf = true) (hb : b.wf = true) : (a.xor b).wf = true := by
  rw [wf_iff] at ha hb ⊢
  change (a.hi ^^^ b.hi).toNat < 2 ^ 48
  rw [UInt64.toNat_xor]
  exact Nat.xor_lt_two_pow ha hb

private theorem wf_zero : V2.zero.wf = true := rfl

private theorem wf_get! {t : Array V2} (ht : ∀ i (h : i < t.size), t[i].wf = true) (i : Nat) :
    (t[i]!).wf = true := by
  by_cases h : i < t.size
  · rw [getElem!_pos t i h]
    exact ht i h
  · rw [getElem!_neg t i h]
    rfl

private theorem wf_getD {t : Array V2} (ht : ∀ i (h : i < t.size), t[i].wf = true) (i : Nat) :
    (t[i]?.getD V2.zero).wf = true := by
  by_cases h : i < t.size
  · rw [getElem?_pos t i h, Option.getD_some]
    exact ht i h
  · rw [getElem?_neg t i h, Option.getD_none]
    exact wf_zero

private theorem wf_frEntry {Y : Array V2} (hY : ∀ i (h : i < Y.size), Y[i].wf = true) (k c : Nat) :
    (frEntry Y k c).wf = true := by
  have key : ∀ (L : List Nat) (acc : V2), acc.wf = true → (L.foldl (fun acc j =>
      if (c >>> j) % 2 = 1 then acc.xor (Y[8 * k + j]?.getD V2.zero) else acc)
      acc).wf = true := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons a L ih =>
      intro acc hacc
      rw [List.foldl_cons]
      apply ih
      split
      · exact wf_xor hacc (wf_getD hY _)
      · exact hacc
  exact key (List.range 8) _ wf_zero

private theorem wf_frTable {Y : Array V2} (hY : ∀ i (h : i < Y.size), Y[i].wf = true) :
    ∀ i (h : i < (frTable Y).size), (frTable Y)[i].wf = true := by
  have hmem : ∀ x ∈ frTable Y, x.wf = true := by
    intro x hx
    unfold frTable at hx
    rw [Array.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact wf_frEntry hY _ _
  intro i h
  exact hmem _ (Array.getElem_mem h)

private theorem wf_frApplyT {t : Array V2} (ht : ∀ i (h : i < t.size), t[i].wf = true) (v : V2) :
    (frApply t v).wf = true := by
  have hb : ∀ base w s acc, acc.wf = true → (frByte t base w s acc).wf = true :=
    fun _ _ _ _ h => wf_xor h (wf_get! ht _)
  unfold frApply frWord6 frWord
  exact hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _
    (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _ (hb _ _ _ _
    (hb _ _ _ _ wf_zero)))))))))))))

private theorem foldr_bits (g : Nat → Nat) (L : List Nat) (k : Nat) :
    (L.foldr (fun i acc => Nat.lor (g i) acc) 0).testBit k = L.any (fun i => (g i).testBit k) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.foldr_cons, List.any_cons, ← ih]
    exact Nat.testBit_or _ _ _

private theorem encR_bits (X : Array V2) (k : Nat) :
    (encR X).testBit k = (List.range 112).any (fun i =>
      decide (128 * i ≤ k) && (v2N (X.getD i V2.zero)).testBit (k - 128 * i)) := by
  unfold encR
  rw [foldr_bits]
  congr 1
  funext i
  change ((v2N (X.getD i V2.zero)) <<< (128 * i)).testBit k = _
  rw [Nat.testBit_shiftLeft]

private theorem rep_bits (s k : Nat) : ∀ m, (rep 1 s m).testBit k =
    (List.range m).any (fun i => decide (k = s * i))
  | 0 => by simp [rep]
  | m + 1 => by
    have e : rep 1 s (m + 1) = rep 1 s m ||| (2 ^ (s * m)) := by
      change Nat.lor (rep 1 s m) (Nat.shiftLeft 1 (Nat.mul s m)) = _
      rw [CFSG.KS.PackFld.shl_eq, Nat.one_mul]
      rfl
    rw [e, Nat.testBit_or, rep_bits s k m, List.range_succ, List.any_append, Nat.testBit_two_pow]
    simp [eq_comm]

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem consts_one {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (h : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : one = rep 1 129 112 := by
  unfold Consts constsOK at h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h, -⟩ := andB_true h
  exact Nat.eq_of_beq_eq_true h

private theorem v2N_lt (v : V2) : v2N v < 2 ^ 128 := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  rw [v2N_testBit]
  have h1 : ¬ k < 64 := by omega
  rw [ite_eq_right h1]
  exact Nat.testBit_lt_two_pow
    (Nat.lt_of_lt_of_le (lt64 v.hi) (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem wf_bit {v : V2} (hv : v.wf = true) {k : Nat} (hk : 112 ≤ k) :
    (v2N v).testBit k = false := by
  rw [wf_iff] at hv
  rw [v2N_testBit]
  have h1 : ¬ k < 64 := by omega
  rw [ite_eq_right h1]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem testBit_V2 (a : V2) {j : Nat} (hj : j < 128) :
    a.testBit j = (v2N a).testBit j := by
  have hm : (UInt64.ofNat (j % 64)).toNat = j % 64 := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ w : UInt64,
      (((w >>> UInt64.ofNat (j % 64)) &&& 1) == 1) = w.toNat.testBit (j % 64) := by
    intro w
    have e : ((w >>> UInt64.ofNat (j % 64)) &&& 1).toNat = w.toNat / 2 ^ (j % 64) % 2 := by
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hm, Nat.mod_eq_of_lt (by omega : j % 64 < 64),
        UInt64.toNat_one, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, ← UInt64.toNat_inj, e, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff,
      UInt64.toNat_one]
  unfold V2.testBit V2.word
  rw [v2N_testBit]
  by_cases h : j < 64
  · have h0 : j / 64 = 0 := Nat.div_eq_of_lt h
    rw [ite_eq_left h0, ite_eq_left h, key, Nat.mod_eq_of_lt h]
  · have h0 : ¬ j / 64 = 0 := by omega
    have hj' : j % 64 = j - 64 := by omega
    rw [ite_eq_right h0, ite_eq_right h, key, hj']

theorem encR_bit (X : Array V2) (p : Nat) :
    (encR X).testBit p =
      (decide (p / 128 < 112) && (v2N (X[p / 128]?.getD V2.zero)).testBit (p % 128)) := by
  rw [encR_bits]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Array.getD_eq_getD_getElem?]
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    have hlt : p - 128 * i < 128 := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt _)
        (Nat.pow_le_pow_right (by omega) (by omega)))] at h2
      exact Bool.false_ne_true h2
    have e1 : p / 128 = i := by omega
    have e2 : p % 128 = p - 128 * i := by omega
    rw [e1, e2]
    exact ⟨hi, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p / 128, h1, by omega, ?_⟩
    have e2 : p - 128 * (p / 128) = p % 128 := by omega
    rw [e2]
    exact h2

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private noncomputable def colm (s n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Bool.rec (motive := fun _ => Nat) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) c)) acc
      (Nat.beq (Nat.land c s) (nat_lit 0))) n

private noncomputable def rowm (s row n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft row (Nat.mul (nat_lit 128) r)))
      (Nat.beq (Nat.land r s) (nat_lit 0))) n

private theorem tmask_eq (k : Nat) : tmask k = rowm (Nat.shiftLeft (nat_lit 1) k)
    (colm (Nat.shiftLeft (nat_lit 1) k) (nat_lit 128)) (nat_lit 128) := by
  unfold tmask rowm colm
  rfl

private theorem colm_succ (s n : Nat) : colm s (n + 1) =
    if Nat.beq (n &&& s) 0 = true then colm s n else colm s n ||| 1 <<< n := by
  change Bool.rec (motive := fun _ => Nat) (colm s n ||| 1 <<< n) (colm s n)
    (Nat.beq (n &&& s) 0) = _
  cases Nat.beq (n &&& s) 0 <;> rfl

private theorem rowm_succ (s row n : Nat) : rowm s row (n + 1) =
    if Nat.beq (n &&& s) 0 = true then rowm s row n ||| row <<< (128 * n) else rowm s row n := by
  change Bool.rec (motive := fun _ => Nat) (rowm s row n) (rowm s row n ||| row <<< (128 * n))
    (Nat.beq (n &&& s) 0) = _
  cases Nat.beq (n &&& s) 0 <;> rfl

private theorem colm_bits (s j : Nat) : ∀ n,
    (colm s n).testBit j = (decide (j < n) && !Nat.beq (j &&& s) 0)
  | 0 => by simp [colm]
  | n + 1 => by
    rw [colm_succ]
    by_cases e : j = n
    · subst e
      cases h : Nat.beq (j &&& s) 0
      · simp [Nat.testBit_or, colm_bits s j j, h, Nat.one_shiftLeft]
      · simp [colm_bits s j j, h]
    · have e' : j < n + 1 ↔ j < n := by omega
      have e2 : ¬ n = j := fun h => e h.symm
      cases h : Nat.beq (n &&& s) 0 <;>
        simp [colm_bits s j n, e', Nat.testBit_or, e2, Nat.one_shiftLeft]

private theorem shl_row_bit {row : Nat} (h : row < 2 ^ 128) (n p : Nat) :
    (row <<< (128 * n)).testBit p = (decide (p / 128 = n) && row.testBit (p % 128)) := by
  rw [Nat.testBit_shiftLeft]
  by_cases e : p / 128 = n
  · have e1 : p - 128 * n = p % 128 := by omega
    have e2 : 128 * n ≤ p := by omega
    simp [e, e1, e2]
  · by_cases e2 : 128 * n ≤ p
    · have e3 : 128 ≤ p - 128 * n := by omega
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) e3))]
      simp [e]
    · simp [e, e2]

private theorem rowm_bits (s : Nat) {row : Nat} (hrow : row < 2 ^ 128) (p : Nat) : ∀ n,
    (rowm s row n).testBit p =
      (decide (p / 128 < n) && Nat.beq (p / 128 &&& s) 0 && row.testBit (p % 128))
  | 0 => by simp [rowm]
  | n + 1 => by
    rw [rowm_succ]
    by_cases e : p / 128 = n
    · cases h : Nat.beq (n &&& s) 0
      · simp [rowm_bits s hrow p n, e, h]
      · simp [Nat.testBit_or, rowm_bits s hrow p n, shl_row_bit hrow, e, h]
    · have e' : p / 128 < n + 1 ↔ p / 128 < n := by omega
      cases h : Nat.beq (n &&& s) 0 <;>
        simp [Nat.testBit_or, rowm_bits s hrow p n, shl_row_bit hrow, e, e']

private theorem beq_and_two_pow (j k : Nat) :
    Nat.beq (j &&& Nat.shiftLeft (nat_lit 1) k) 0 = !j.testBit k := by
  change Nat.beq (j &&& 1 <<< k) 0 = _
  cases h : j.testBit k
  · have e : j &&& 1 <<< k = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases e : k = i
      · subst e
        simp [h]
      · simp [e]
    rw [e]
    rfl
  · have e : (j &&& 1 <<< k).testBit k = true := by
      rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self, h]
      rfl
    cases hb : Nat.beq (j &&& 1 <<< k) 0
    · rfl
    · rw [Nat.eq_of_beq_eq_true hb, Nat.zero_testBit] at e
      exact absurd e Bool.false_ne_true

private theorem colm128 (s j : Nat) :
    (colm s (nat_lit 128)).testBit j = (decide (j < 128) && !Nat.beq (j &&& s) 0) :=
  colm_bits s j 128

private theorem rowm128 (s : Nat) {row : Nat} (hrow : row < 2 ^ 128) (p : Nat) :
    (rowm s row (nat_lit 128)).testBit p =
      (decide (p / 128 < 128) && Nat.beq (p / 128 &&& s) 0 && row.testBit (p % 128)) :=
  rowm_bits s hrow p 128

private theorem colm_lt (s : Nat) : colm s (nat_lit 128) < 2 ^ 128 :=
  Nat.lt_pow_two_of_testBit _ (fun j hj => by
    rw [colm128]
    have : ¬ j < 128 := by omega
    simp [this])

private theorem tmask_dec (k p : Nat) : (tmask k).testBit p =
    decide (p / 128 < 128 ∧ p / 128 / 2 ^ k % 2 = 0 ∧ p % 128 / 2 ^ k % 2 = 1) := by
  rw [tmask_eq, rowm128 _ (colm_lt _), colm128, beq_and_two_pow, beq_and_two_pow,
    Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  have hc : p % 128 < 128 := Nat.mod_lt _ (by omega)
  rcases Nat.mod_two_eq_zero_or_one (p / 128 / 2 ^ k) with h | h <;> simp [h, hc]

private noncomputable def piK (s p : Nat) : Nat :=
  if p / 128 < 128 ∧ p / 128 / s % 2 = 0 ∧ p % 128 / s % 2 = 1 then p + 127 * s
  else if p / 128 < 128 ∧ p / 128 / s % 2 = 1 ∧ p % 128 / s % 2 = 0 then p - 127 * s else p

private theorem lvl_bit {k s : Nat} (hk : k < 7) (hs : s = 2 ^ k) (x p : Nat) :
    (trLvl s (tmask k) x).testBit p = x.testBit (piK s p) := by
  unfold trLvl
  rw [strictN_eq', strictN_eq']
  change (x ^^^ (((x ^^^ x >>> (127 * s)) &&& tmask k) |||
    ((x ^^^ x >>> (127 * s)) &&& tmask k) <<< (127 * s))).testBit p = _
  have hs7 : s = 1 ∨ s = 2 ∨ s = 4 ∨ s = 8 ∨ s = 16 ∨ s = 32 ∨ s = 64 := by
    subst hs
    interval_cases k <;> simp
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, tmask_dec, ← hs]
  unfold piK
  by_cases h1 : p / 128 < 128 ∧ p / 128 / s % 2 = 0 ∧ p % 128 / s % 2 = 1
  · have h3 : 127 * s ≤ p → ¬ ((p - 127 * s) / 128 < 128 ∧ (p - 127 * s) / 128 / s % 2 = 0 ∧
        (p - 127 * s) % 128 / s % 2 = 1) := by
      rcases hs7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    rw [ite_eq_left h1, Nat.add_comm (127 * s) p]
    by_cases h4 : 127 * s ≤ p
    · simp [h1, h3 h4, h4]
    · simp [h1, h4]
  · rw [ite_eq_right h1]
    by_cases h2 : p / 128 < 128 ∧ p / 128 / s % 2 = 1 ∧ p % 128 / s % 2 = 0
    · have h4 : 127 * s ≤ p ∧ ((p - 127 * s) / 128 < 128 ∧ (p - 127 * s) / 128 / s % 2 = 0 ∧
          (p - 127 * s) % 128 / s % 2 = 1) := by
        rcases hs7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [ite_eq_left h2, Nat.add_sub_cancel' h4.1]
      simp only [h1, h4, decide_false, decide_true, Bool.and_false, Bool.false_or, Bool.true_and]
      cases x.testBit p <;> cases x.testBit (p - 127 * s) <;> rfl
    · have h3 : 127 * s ≤ p → ¬ ((p - 127 * s) / 128 < 128 ∧ (p - 127 * s) / 128 / s % 2 = 0 ∧
          (p - 127 * s) % 128 / s % 2 = 1) := by
        rcases hs7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      rw [ite_eq_right h2]
      by_cases h4 : 127 * s ≤ p
      · simp [h1, h3 h4, h4]
      · simp [h1, h4]

private def posB (a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Nat) : Nat :=
  128 * (a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6) +
    (b0 + 2 * b1 + 4 * b2 + 8 * b3 + 16 * b4 + 32 * b5 + 64 * b6)

section Swap

variable {a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 : Nat} (h0 : a0 ≤ 1) (h1 : a1 ≤ 1)
  (h2 : a2 ≤ 1) (h3 : a3 ≤ 1) (h4 : a4 ≤ 1) (h5 : a5 ≤ 1) (h6 : a6 ≤ 1) (g0 : b0 ≤ 1)
  (g1 : b1 ≤ 1) (g2 : b2 ≤ 1) (g3 : b3 ≤ 1) (g4 : b4 ≤ 1) (g5 : b5 ≤ 1) (g6 : b6 ≤ 1)
include h0 h1 h2 h3 h4 h5 h6 g0 g1 g2 g3 g4 g5 g6

private theorem piK0 : piK 1 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB b0 a1 a2 a3 a4 a5 a6 a0 b1 b2 b3 b4 b5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK1 : piK 2 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 b1 a2 a3 a4 a5 a6 b0 a1 b2 b3 b4 b5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK2 : piK 4 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 a1 b2 a3 a4 a5 a6 b0 b1 a2 b3 b4 b5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK3 : piK 8 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 a1 a2 b3 a4 a5 a6 b0 b1 b2 a3 b4 b5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK4 : piK 16 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 a1 a2 a3 b4 a5 a6 b0 b1 b2 b3 a4 b5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK5 : piK 32 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 a1 a2 a3 a4 b5 a6 b0 b1 b2 b3 b4 a5 b6 := by
  unfold piK posB
  split_ifs <;> omega

private theorem piK6 : piK 64 (posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6) =
    posB a0 a1 a2 a3 a4 a5 b6 b0 b1 b2 b3 b4 b5 a6 := by
  unfold piK posB
  split_ifs <;> omega

end Swap

private theorem bits7 {r : Nat} (hr : r < 128) : ∃ a0 a1 a2 a3 a4 a5 a6 : Nat, a0 ≤ 1 ∧ a1 ≤ 1 ∧
    a2 ≤ 1 ∧ a3 ≤ 1 ∧ a4 ≤ 1 ∧ a5 ≤ 1 ∧ a6 ≤ 1 ∧
    r = a0 + 2 * a1 + 4 * a2 + 8 * a3 + 16 * a4 + 32 * a5 + 64 * a6 :=
  ⟨r % 2, r / 2 % 2, r / 4 % 2, r / 8 % 2, r / 16 % 2, r / 32 % 2, r / 64 % 2, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem piK_big {s p : Nat} (h : 128 ≤ p / 128) : piK s p = p := by
  unfold piK
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem piK_all (p : Nat) :
    piK 64 (piK 32 (piK 16 (piK 8 (piK 4 (piK 2 (piK 1 p)))))) =
      if p / 128 < 128 then 128 * (p % 128) + p / 128 else p := by
  by_cases hp : p / 128 < 128
  · rw [ite_eq_left hp]
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, ha⟩ := bits7 hp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, g0, g1, g2, g3, g4, g5, g6, hb⟩ :=
      bits7 (Nat.mod_lt p (by omega : 128 > 0))
    have e : p = posB a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 := by
      unfold posB
      omega
    rw [ha, hb, e, piK0 h0 h1 h2 h3 h4 h5 h6 g0 g1 g2 g3 g4 g5 g6,
      piK1 g0 h1 h2 h3 h4 h5 h6 h0 g1 g2 g3 g4 g5 g6,
      piK2 g0 g1 h2 h3 h4 h5 h6 h0 h1 g2 g3 g4 g5 g6,
      piK3 g0 g1 g2 h3 h4 h5 h6 h0 h1 h2 g3 g4 g5 g6,
      piK4 g0 g1 g2 g3 h4 h5 h6 h0 h1 h2 h3 g4 g5 g6,
      piK5 g0 g1 g2 g3 g4 h5 h6 h0 h1 h2 h3 h4 g5 g6,
      piK6 g0 g1 g2 g3 g4 g5 h6 h0 h1 h2 h3 h4 h5 g6]
    unfold posB
    omega
  · rw [ite_eq_right hp]
    have hb : 128 ≤ p / 128 := by omega
    rw [piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb, piK_big hb]

private theorem trJ_bit (x p : Nat) :
    (trJ (tmask 0) (tmask 1) (tmask 2) (tmask 3) (tmask 4) (tmask 5) (tmask 6) x).testBit p =
      x.testBit (if p / 128 < 128 then 128 * (p % 128) + p / 128 else p) := by
  change (trLvl 1 (tmask 0) (trLvl 2 (tmask 1) (trLvl 4 (tmask 2) (trLvl 8 (tmask 3)
    (trLvl 16 (tmask 4) (trLvl 32 (tmask 5) (trLvl 64 (tmask 6) x))))))).testBit p = _
  rw [lvl_bit (k := 0) (s := 1) (by omega) rfl, lvl_bit (k := 1) (s := 2) (by omega) rfl,
    lvl_bit (k := 2) (s := 4) (by omega) rfl, lvl_bit (k := 3) (s := 8) (by omega) rfl,
    lvl_bit (k := 4) (s := 16) (by omega) rfl, lvl_bit (k := 5) (s := 32) (by omega) rfl,
    lvl_bit (k := 6) (s := 64) (by omega) rfl, piK_all]

private theorem consts_t {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (h : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) :
    t0 = tmask 0 ∧ t1 = tmask 1 ∧ t2 = tmask 2 ∧ t3 = tmask 3 ∧ t4 = tmask 4 ∧ t5 = tmask 5 ∧
      t6 = tmask 6 := by
  unfold Consts constsOK at h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨e0, h⟩ := andB_true h
  obtain ⟨e1, h⟩ := andB_true h
  obtain ⟨e2, h⟩ := andB_true h
  obtain ⟨e3, h⟩ := andB_true h
  obtain ⟨e4, h⟩ := andB_true h
  obtain ⟨e5, e6⟩ := andB_true h
  exact ⟨Nat.eq_of_beq_eq_true e0, Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2,
    Nat.eq_of_beq_eq_true e3, Nat.eq_of_beq_eq_true e4, Nat.eq_of_beq_eq_true e5,
    Nat.eq_of_beq_eq_true e6⟩

theorem consts_c {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (h : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : c = rep 1 128 112 ∧ rm = 2 ^ 112 - 1 := by
  unfold Consts constsOK at h
  obtain ⟨hc, h⟩ := andB_true h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨hr, -⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true hc, ?_⟩
  rw [Nat.eq_of_beq_eq_true hr]
  change 1 <<< 112 - 1 = _
  rw [Nat.one_shiftLeft]

@[expose] noncomputable def xsum (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc => acc ^^^ f k) n

theorem xsum_succ (f : Nat → Nat) (n : Nat) : xsum f (n + 1) = xsum f n ^^^ f n := rfl

theorem xsum_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = g k) →
    xsum f n = xsum g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [xsum_succ, xsum_succ, xsum_congr (fun k hk => h k (by omega)), h n (by omega)]

theorem xsum_zero {f : Nat → Nat} : ∀ {n : Nat}, (∀ k < n, f k = 0) → xsum f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [xsum_succ, xsum_zero (fun k hk => h k (by omega)), h n (by omega)]
    rfl

theorem xsum_add (f : Nat → Nat) (a : Nat) : ∀ b,
    xsum f (a + b) = xsum f a ^^^ xsum (fun i => f (a + i)) b
  | 0 => by rw [Nat.add_zero]; exact (Nat.xor_zero _).symm
  | b + 1 => by
    rw [← Nat.add_assoc, xsum_succ, xsum_add f a b, xsum_succ, Nat.xor_assoc]

theorem xsum_blocks (f : Nat → Nat) : ∀ n,
    xsum f (8 * n) = xsum (fun q => xsum (fun i => f (8 * q + i)) 8) n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.mul_succ, xsum_add, xsum_blocks f n]
    rfl

private theorem v2N_xor (a b : V2) : v2N (a.xor b) = v2N a ^^^ v2N b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, v2N_testBit, v2N_testBit, v2N_testBit]
  change (if j < 64 then (a.lo ^^^ b.lo).toNat.testBit j else (a.hi ^^^ b.hi).toNat.testBit (j - 64)) = _
  rw [UInt64.toNat_xor, UInt64.toNat_xor, Nat.testBit_xor, Nat.testBit_xor]
  by_cases h : j < 64 <;> simp [h]

theorem v2N_zero: v2N V2.zero = 0 := rfl

private theorem frEntry_v2N (Y : Array V2) (k c : Nat) : v2N (frEntry Y k c) =
    xsum (fun i => if c.testBit i then v2N (Y[8 * k + i]?.getD V2.zero) else 0) 8 := by
  have key : ∀ n, v2N ((List.range n).foldl (fun acc i =>
      if (c >>> i) % 2 = 1 then acc.xor (Y[8 * k + i]?.getD V2.zero) else acc) V2.zero) =
      xsum (fun i => if c.testBit i then v2N (Y[8 * k + i]?.getD V2.zero) else 0) n := by
    intro n
    induction n with
    | zero =>
      rw [List.range_zero, List.foldl_nil]
      rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, xsum_succ, ← ih]
      have hc : ((c >>> n) % 2 = 1) ↔ c.testBit n = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, decide_eq_true_iff]
      by_cases h : c.testBit n = true
      · rw [ite_eq_left (hc.mpr h), ite_eq_left h, v2N_xor]
      · rw [ite_eq_right (fun e => h (hc.mp e)), ite_eq_right h, Nat.xor_zero]
  exact key 8

private theorem frTable_get (Y : Array V2) {i : Nat} (hi : i < 3584) :
    (frTable Y)[i]! = frEntry Y (i / 256) (i % 256) := by
  unfold frTable
  rw [getElem!_pos _ _ (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]

private theorem ff_toNat : (0xFF : UInt64).toNat = 2 ^ 8 - 1 := rfl

private theorem frByte_eq (Y : Array V2) {base : Nat} (w s : UInt64) (acc : V2)
    (h1 : base % 256 = 0) (h2 : base < 3584) :
    v2N (frByte (frTable Y) base w s acc) =
      v2N acc ^^^ v2N (frEntry Y (base / 256) ((w >>> s) &&& 0xFF).toNat) := by
  have hb : ((w >>> s) &&& 0xFF).toNat < 256 := by
    rw [UInt64.toNat_and, ff_toNat, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by omega)
  unfold frByte
  rw [v2N_xor, frTable_get Y (by omega)]
  have e1 : (base + ((w >>> s) &&& 0xFF).toNat) / 256 = base / 256 := by omega
  have e2 : (base + ((w >>> s) &&& 0xFF).toNat) % 256 = ((w >>> s) &&& 0xFF).toNat := by omega
  rw [e1, e2]

private theorem byte_lo (v : V2) (s : UInt64) (hs : s.toNat ≤ 56) :
    ((v.lo >>> s) &&& 0xFF).toNat = (v2N v >>> s.toNat) % 2 ^ 8 := by
  rw [UInt64.toNat_and, ff_toNat, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt (by omega : s.toNat < 64)]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, v2N_testBit]
  by_cases hj : j < 8
  · have : s.toNat + j < 64 := by omega
    simp [hj, this]
  · simp [hj]

private theorem byte_hi (v : V2) (s : UInt64) (hs : s.toNat ≤ 40) :
    ((v.hi >>> s) &&& 0xFF).toNat = (v2N v >>> (64 + s.toNat)) % 2 ^ 8 := by
  rw [UInt64.toNat_and, ff_toNat, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftRight,
    Nat.mod_eq_of_lt (by omega : s.toNat < 64)]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Nat.testBit_shiftRight, v2N_testBit]
  have h1 : ¬ 64 + s.toNat + j < 64 := by omega
  have h2 : 64 + s.toNat + j - 64 = s.toNat + j := by omega
  rw [ite_eq_right h1, h2]

private theorem fr_core (Y : Array V2) (v : V2) : v2N (frApply (frTable Y) v) =
    xsum (fun k => if (v2N v).testBit k then v2N (Y[k]?.getD V2.zero) else 0) 112 := by
  have E : ∀ q, v2N (frEntry Y q ((v2N v >>> (8 * q)) % 2 ^ 8)) =
      xsum (fun i => if (v2N v).testBit (8 * q + i) then v2N (Y[8 * q + i]?.getD V2.zero) else 0)
        8 := by
    intro q
    rw [frEntry_v2N]
    apply xsum_congr
    intro i hi
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hi]
  have H : v2N (frApply (frTable Y) v) =
      xsum (fun q => v2N (frEntry Y q ((v2N v >>> (8 * q)) % 2 ^ 8))) 14 := by
    simp (disch := decide) only [frApply, frWord6, frWord, frByte_eq Y, byte_lo v, byte_hi v,
      v2N_zero]
    rfl
  rw [H, show (112 : Nat) = 8 * 14 from rfl, xsum_blocks]
  exact xsum_congr (fun q _ => E q)

theorem rowJ_eq {X : Array V2} (hX : ∀ i (h : i < X.size), X[i].wf = true) {k : Nat}
    (hk : k < 112) : rowJ (2 ^ 112 - 1) (encR X) k = v2N (X[k]?.getD V2.zero) := by
  apply Nat.eq_of_testBit_eq
  intro j
  change ((encR X >>> (k * 128)) &&& (2 ^ 112 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, encR_bit]
  by_cases hj : j < 112
  · have e1 : (k * 128 + j) / 128 = k := by omega
    have e2 : (k * 128 + j) % 128 = j := by omega
    rw [e1, e2]
    simp [hj, hk]
  · rw [wf_bit (wf_getD hX k) (by omega)]
    simp [hj]

theorem and_one_bit (x k : Nat) : (x >>> k) &&& 1 = if x.testBit k then 1 else 0 := by
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

open CFSG.KS.PackFld in
private theorem fld_xor {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A ^^^ B) (fun i => g i ^^^ h i) := by
  intro i k hk
  rw [Nat.testBit_xor, hA i k hk, hB i k hk, Nat.testBit_xor]

open CFSG.KS.PackFld in
private theorem fld_and {w A B : Nat} {g h : Nat → Nat} (hA : Fld w A g) (hB : Fld w B h) :
    Fld w (A &&& B) (fun i => g i &&& h i) := by
  intro i k hk
  rw [Nat.testBit_and, hA i k hk, hB i k hk, Nat.testBit_and]

open CFSG.KS.PackFld in
private theorem fld_eq {w X Y : Nat} {g : Nat → Nat} (hw : 0 < w) (hX : Fld w X g)
    (hY : Fld w Y g) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro p
  have hd := Nat.div_add_mod p w
  rw [← hd, hX _ _ (Nat.mod_lt _ hw), hY _ _ (Nat.mod_lt _ hw)]

open CFSG.KS.PackFld in
private theorem fld_xsum {P : Nat → Nat} {G : Nat → Nat → Nat} : ∀ {n : Nat},
    (∀ k < n, Fld 128 (P k) (G k)) → Fld 128 (xsum P n) (fun i => xsum (fun k => G k i) n)
  | 0, _ => fld_congr (fld_zero 128) (fun _ => rfl)
  | n + 1, h => fld_congr (fld_xor (fld_xsum (fun k hk => h k (by omega))) (h n (by omega)))
      (fun _ => rfl)

open CFSG.KS.PackFld in
private theorem encR_fld (X : Array V2) :
    Fld 128 (encR X) (fun i => if i < 112 then v2N (X[i]?.getD V2.zero) else 0) := by
  intro i k hk
  rw [encR_bit]
  have e1 : (128 * i + k) / 128 = i := by omega
  have e2 : (128 * i + k) % 128 = k := by omega
  rw [e1, e2]
  by_cases hi : i < 112
  · simp [hi]
  · simp [hi]

private noncomputable def bsum (h : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc + h i * 2 ^ (128 * i)) n

private theorem bsum_succ (h : Nat → Nat) (n : Nat) :
    bsum h (n + 1) = bsum h n + h n * 2 ^ (128 * n) := rfl

open CFSG.KS.PackFld in
private theorem fld_bsum {h : Nat → Nat} (hh : ∀ i, h i < 2 ^ 128) : ∀ n,
    Fld 128 (bsum h n) (fun i => if i < n then h i else 0) ∧ bsum h n < 2 ^ (128 * n)
  | 0 => ⟨fld_congr (fld_zero 128) (fun i => by simp), by simp [bsum]⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := fld_bsum hh n
    have e : bsum h (n + 1) = h n <<< (128 * n) ||| bsum h n := by
      rw [bsum_succ, Nat.add_comm, ← Nat.shiftLeft_eq, Nat.shiftLeft_add_eq_or_of_lt ih2]
    refine ⟨?_, ?_⟩
    · rw [e]
      refine fld_congr (fld_or (fld_shl n (fld_one (hh n))) ih1) ?_
      intro i
      by_cases h1 : i < n
      · have h2 : ¬ n ≤ i := by omega
        have h3 : i < n + 1 := by omega
        simp [h1, h2, h3]
      · by_cases h2 : i = n
        · subst h2
          simp
        · have h3 : ¬ i < n + 1 := by omega
          have h4 : ¬ i - n = 0 := by omega
          simp [h1, h3, h4]
    · rw [bsum_succ]
      have h3 : h n * 2 ^ (128 * n) + 2 ^ (128 * n) ≤ 2 ^ 128 * 2 ^ (128 * n) := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ (hh n)
      rw [Nat.mul_succ, Nat.add_comm (128 * n) 128, Nat.pow_add]
      omega

private theorem bsum_mul (h : Nat → Nat) (v : Nat) : ∀ n, bsum h n * v = bsum (fun i => h i * v) n
  | 0 => by simp [bsum]
  | n + 1 => by
    rw [bsum_succ, bsum_succ, Nat.add_mul, bsum_mul h v n, Nat.mul_right_comm]

private theorem one_bit (k : Nat) : (1 : Nat).testBit k = decide (k = 0) := by
  rw [← Nat.pow_zero 2, Nat.testBit_two_pow]
  simp [eq_comm]

open CFSG.KS.PackFld in
private theorem c_eq : rep 1 128 112 = bsum (fun _ => 1) 112 := by
  refine fld_eq (by omega : 0 < 128) (g := fun i => if i < 112 then 1 else 0) ?_
    ((fld_bsum (fun _ => by omega) 112).1)
  intro i k hk
  rw [rep_bits]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  by_cases hi : i < 112
  · rw [ite_eq_left hi, one_bit]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨l, hl, e⟩
      omega
    · intro e
      exact ⟨i, hi, by omega⟩
  · rw [ite_eq_right hi, Nat.zero_testBit]
    simp only [Bool.false_eq_true, iff_false, not_exists, not_and]
    intro l hl e
    omega

private noncomputable def stepP (c rm a b k : Nat) : Nat :=
  ((a >>> k) &&& c) * rm &&& ((b >>> (k * 128)) &&& rm) * c

private theorem mrec_eq (c rm a b : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => mstep c rm a b acc k) n = xsum (stepP c rm a b) n
  | 0 => rfl
  | n + 1 => by
    change mstep c rm a b (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => mstep c rm a b acc k) n) n = _
    rw [mrec_eq c rm a b n]
    rfl

private theorem mulJ_eq (c rm a b : Nat) : mulJ c rm a b = xsum (stepP c rm a b) (nat_lit 112) := by
  unfold mulJ
  rw [strictN_eq', strictN_eq']
  exact mrec_eq c rm a b (nat_lit 112)

private theorem vrec_eq (rm x m : Nat) : ∀ n, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight x k) (nat_lit 1)) (rowJ rm m k)))
    n = xsum (fun k => ((x >>> k) &&& 1) * rowJ rm m k) n
  | 0 => rfl
  | n + 1 => by
    change Nat.xor (Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc
      (Nat.mul (Nat.land (Nat.shiftRight x k) (nat_lit 1)) (rowJ rm m k))) n)
      (Nat.mul (Nat.land (Nat.shiftRight x n) (nat_lit 1)) (rowJ rm m n)) = _
    rw [vrec_eq rm x m n]
    rfl

theorem vecJ_eq (rm x m : Nat) :
    vecJ rm x m = xsum (fun k => ((x >>> k) &&& 1) * rowJ rm m k) (nat_lit 112) := by
  unfold vecJ
  rw [strictN_eq', strictN_eq']
  exact vrec_eq rm x m (nat_lit 112)

open CFSG.KS.PackFld in
private theorem fld_stepP {X Y : Array V2} (hY : ∀ i (h : i < Y.size), Y[i].wf = true) {k : Nat}
    (hk : k < 112) : Fld 128 (stepP (rep 1 128 112) (2 ^ 112 - 1) (encR X) (encR Y) k)
      (fun i => if i < 112 then
        (if (v2N (X[i]?.getD V2.zero)).testBit k then v2N (Y[k]?.getD V2.zero) else 0) else 0) := by
  have hrm : 2 ^ 112 - 1 < 2 ^ 112 := by omega
  have hx : Fld 128 ((encR X >>> k) &&& rep 1 128 112) (fun i => if i < 112 then
      (if (v2N (X[i]?.getD V2.zero)).testBit k then 1 else 0) else 0) := by
    intro i j hj
    have hc := (fld_bsum (h := fun _ => 1) (fun _ => by omega) 112).1 i j hj
    rw [← c_eq] at hc
    dsimp only at hc ⊢
    rw [Nat.testBit_and, Nat.testBit_shiftRight, hc]
    by_cases hi : i < 112
    · rw [ite_eq_left hi, ite_eq_left hi, one_bit]
      by_cases hj0 : j = 0
      · subst hj0
        have e : k + (128 * i + 0) = 128 * i + k := by omega
        rw [e, encR_bit]
        have e1 : (128 * i + k) / 128 = i := by omega
        have e2 : (128 * i + k) % 128 = k := by omega
        rw [e1, e2]
        cases (v2N (X[i]?.getD V2.zero)).testBit k <;> simp [hi]
      · cases (v2N (X[i]?.getD V2.zero)).testBit k <;> simp [hj0, one_bit]
    · rw [ite_eq_right hi, ite_eq_right hi]
      simp
  have hxb : ∀ i : Nat, (if (v2N (X[i]?.getD V2.zero)).testBit k then 1 else 0) * (2 ^ 112 - 1) <
      2 ^ 128 := by
    intro i
    cases (v2N (X[i]?.getD V2.zero)).testBit k <;> simp
  have hxe := fld_eq (by omega : 0 < 128) hx
    (fld_bsum (h := fun i : Nat => if (v2N (X[i]?.getD V2.zero)).testBit k then 1 else 0)
      (fun i => Nat.lt_of_le_of_lt (by split <;> omega) (by omega : 1 < 2 ^ 128)) 112).1
  have hy : (encR Y >>> (k * 128)) &&& (2 ^ 112 - 1) = v2N (Y[k]?.getD V2.zero) := rowJ_eq hY hk
  have hyl : v2N (Y[k]?.getD V2.zero) < 2 ^ 112 := by
    rw [← hy]
    exact Nat.and_lt_two_pow _ hrm
  have h1 : Fld 128 (((encR X >>> k) &&& rep 1 128 112) * (2 ^ 112 - 1))
      (fun i => if i < 112 then
        (if (v2N (X[i]?.getD V2.zero)).testBit k then 1 else 0) * (2 ^ 112 - 1) else 0) := by
    rw [hxe, bsum_mul]
    exact (fld_bsum hxb 112).1
  have h2 : Fld 128 (v2N (Y[k]?.getD V2.zero) * rep 1 128 112)
      (fun i => if i < 112 then 1 * v2N (Y[k]?.getD V2.zero) else 0) := by
    rw [c_eq, Nat.mul_comm, bsum_mul]
    exact (fld_bsum (fun _ => by omega) 112).1
  unfold stepP
  rw [hy]
  refine fld_congr (fld_and h1 h2) ?_
  intro i
  by_cases hi : i < 112
  · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left hi]
    cases (v2N (X[i]?.getD V2.zero)).testBit k
    · simp
    · simp only [↓reduceIte, Nat.one_mul]
      rw [Nat.and_comm, Nat.and_two_pow_sub_one_of_lt_two_pow hyl]
  · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi]
    rfl

private theorem v2N_inj {a b : V2} (h : v2N a = v2N b) : a = b := by
  have hlo : a.lo.toNat = b.lo.toNat := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 64
    · have e := congrArg (fun x => x.testBit j) h
      rw [v2N_testBit, v2N_testBit, ite_eq_left hj, ite_eq_left hj] at e
      exact e
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64 _) (Nat.pow_le_pow_right (by omega)
        (by omega))), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64 _)
        (Nat.pow_le_pow_right (by omega) (by omega)))]
  have hhi : a.hi.toNat = b.hi.toNat := by
    apply Nat.eq_of_testBit_eq
    intro j
    have e := congrArg (fun x => x.testBit (j + 64)) h
    rw [v2N_testBit, v2N_testBit, ite_eq_right (by omega), ite_eq_right (by omega),
      Nat.add_sub_cancel] at e
    exact e
  obtain ⟨al, ah⟩ := a
  obtain ⟨bl, bh⟩ := b
  rw [V2.mk.injEq]
  exact ⟨UInt64.toNat_inj.mp hlo, UInt64.toNat_inj.mp hhi⟩

private theorem beq_iff (a b : V2) : a.beq b = true ↔ v2N a = v2N b := by
  constructor
  · intro h
    obtain ⟨al, ah⟩ := a
    obtain ⟨bl, bh⟩ := b
    unfold V2.beq at h
    dsimp only at h
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    rw [h.1, h.2]
  · intro h
    rw [v2N_inj h]
    unfold V2.beq
    simp

section Prim

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem enc_mulRows (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X Y : Array V2} (_hX : WfA X)
    (_hY : WfA Y) : encR (mulRows X Y) = mulJ c rm (encR X) (encR Y) := by
  obtain ⟨hc, hrm⟩ := consts_c _hK
  subst hc hrm
  have hY : ∀ i (h : i < Y.size), Y[i].wf = true := Array.all_eq_true.mp _hY.2
  rw [mulJ_eq]
  refine fld_eq (by omega : 0 < 128) (encR_fld _)
    (CFSG.KS.PackFld.fld_congr (fld_xsum (fun k hk => fld_stepP (X := X) hY hk)) ?_)
  intro i
  by_cases hi : i < 112
  · rw [ite_eq_left hi]
    have hs : i < X.size := by rw [_hX.1]; exact hi
    have hm : (mulRows X Y)[i]?.getD V2.zero = frApply (frTable Y) (X[i]?.getD V2.zero) := by
      simp [mulRows, hs]
    rw [hm, fr_core]
    exact xsum_congr (fun k _ => ite_eq_left hi)
  · rw [ite_eq_right hi]
    exact xsum_zero (fun k _ => ite_eq_right hi)

theorem wf_mulRows {X Y : Array V2} (_hX : WfA X) (_hY : WfA Y) : WfA (mulRows X Y) := by
  have hY : ∀ y ∈ Y, y.wf = true := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
    exact (Array.all_eq_true.mp _hY.2) i hi
  refine ⟨?_, Array.all_eq_true.mpr ?_⟩
  · rw [CFSG.Sporadic.J4.mulRows_size]
    exact _hX.1
  · intro i hi
    exact CFSG.Sporadic.J4.mulRows_wf X hY _ (Array.getElem_mem hi)

theorem eqRows_eq {X Y : Array V2} (_hX : WfA X) (_hY : WfA Y) :
    eqRows X Y = Nat.beq (encR X) (encR Y) := by
  have hrepr (a : V2) : v2N a = a.toNat := by
    unfold v2N V2.toNat
    rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt a.lo) a.hi.toNat,
      Nat.shiftLeft_eq]
    omega
  have hacc (g : Nat → Nat) (l : List Nat) (z : Nat) :
      l.foldr (fun i acc => Nat.lor (g i) acc) z =
        Nat.lor (l.foldr (fun i acc => Nat.lor (g i) acc) 0) z := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, ih]
      simp only [Nat.lor_eq, Nat.or_assoc]
  have hfold (g : Nat → Nat) : ∀ n,
      (List.range n).foldr (fun i acc => Nat.lor (g i) acc) 0 =
        Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldr_append]
      change (List.range n).foldr (fun i acc => Nat.lor (g i) acc) (Nat.lor (g n) 0) =
        Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n) (g n)
      rw [show Nat.lor (g n) 0 = g n by rw [Nat.lor_eq, Nat.or_zero], hacc, ih]
  let P (u : Nat → Nat) (n : Nat) := Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (u i) (128 * i))) n
  have hbit (u : Nat → Nat) (hu : ∀ i < 112, u i < 2 ^ 128) :
      ∀ n, n ≤ 112 → ∀ j, (P u n).testBit j =
        if j < 128 * n then (u (j / 128)).testBit (j % 128) else false := by
    intro n
    induction n with
    | zero => intro _ j; simp [P]
    | succ n ih =>
      intro hn j
      change (Nat.lor (P u n) (Nat.shiftLeft (u n) (128 * n))).testBit j = _
      rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.testBit_shiftLeft,
        ih (by omega) j]
      by_cases hj : j < 128 * n
      · simp [hj, show ¬j ≥ 128 * n by omega, show j < 128 * (n + 1) by omega]
      · have hnj : 128 * n ≤ j := by omega
        by_cases hjlast : j < 128 * (n + 1)
        · have hdiv : j / 128 = n := by omega
          have hmod : j % 128 = j - 128 * n := by omega
          simp [hj, hnj, hjlast, hdiv, hmod]
        · have hlow : 128 ≤ j - 128 * n := by omega
          have hz : (u n).testBit (j - 128 * n) = false :=
            Nat.testBit_lt_two_pow ((hu n (by omega)).trans_le
              (Nat.pow_le_pow_right (by norm_num) hlow))
          simp [hj, hnj, hjlast, hz]
  have hencBit (Z : Array V2) (j : Nat) :
      (encR Z).testBit j = if j < 128 * 112 then
        (v2N (Z.getD (j / 128) V2.zero)).testBit (j % 128) else false := by
    unfold encR
    rw [hfold]
    exact hbit (fun i => v2N (Z.getD i V2.zero))
      (fun i _ => by rw [hrepr]; exact V2.toNat_lt _) 112 (Nat.le_refl 112) j
  have hinj (he : encR X = encR Y) : X = Y := by
    apply Array.ext (_hX.1.trans _hY.1.symm)
    intro i hi hj
    apply V2.toNat_injective
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < 128
    · have h := congrArg (fun z : Nat => z.testBit (128 * i + b)) he
      rw [hencBit X _, hencBit Y _] at h
      have hi' : i < 112 := by simpa only [_hX.1] using hi
      have hbound : 128 * i + b < 128 * 112 := by omega
      have hdiv : (128 * i + b) / 128 = i := by omega
      have hmod : (128 * i + b) % 128 = b := by omega
      simp only [if_pos hbound, hdiv, hmod] at h
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
        Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj, Option.getD_some] at h
      simpa only [hrepr] using h
    · have hle : 2 ^ 128 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow ((V2.toNat_lt _).trans_le hle),
        Nat.testBit_lt_two_pow ((V2.toNat_lt _).trans_le hle)]
  rw [Bool.eq_iff_iff, CFSG.Sporadic.J4.eqRows_iff, Nat.beq_eq]
  constructor
  · rintro rfl; rfl
  · exact hinj

theorem enc_idRows (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : encR (idRows ()) = one := by
  have hand (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
    cases a <;> cases b <;> simp [andB]
  have hk := _hK
  unfold Consts constsOK at hk
  have hk1 := ((hand _ _).mp hk).2
  have hk2 := ((hand _ _).mp hk1).2
  have hk3 := ((hand _ _).mp hk2).2
  have hone : one = rep 1 129 112 := Nat.beq_eq.mp (((hand _ _).mp hk3).1)
  have hrepr (v : V2) : v2N v = v.toNat := by
    unfold v2N V2.toNat
    rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt v.lo) v.hi.toNat,
      Nat.shiftLeft_eq]
    omega
  have hrow (i : Nat) (hi : i < 112) : v2N ((idRows ()).getD i V2.zero) = 2 ^ i := by
    have heq : (idRows ()).getD i V2.zero = V2.ofFn (fun j => j == i) := by
      simp [idRows, Array.getD_eq_getD_getElem?, hi]
    rw [heq, hrepr]
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 112
    · rw [V2.testBit_toNat _ (by omega), V2.ofFn_testBit _ hj, Nat.testBit_two_pow]
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq]
      exact eq_comm
    · have hlt : (V2.ofFn (fun j => j == i)).toNat < 2 ^ j :=
        ((V2.wf_iff_toNat_lt _).mp (V2.ofFn_wf _)).trans_le
          (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hlt, Nat.testBit_two_pow_of_ne (by omega)]
  have hacc (g : Nat → Nat) (l : List Nat) (z : Nat) :
      l.foldr (fun i acc => Nat.lor (g i) acc) z =
        Nat.lor (l.foldr (fun i acc => Nat.lor (g i) acc) 0) z := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.foldr_cons, ih]
      simp only [Nat.lor_eq, Nat.or_assoc]
  have hfold (g : Nat → Nat) : ∀ n,
      (List.range n).foldr (fun i acc => Nat.lor (g i) acc) 0 =
        Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldr_append]
      change (List.range n).foldr (fun i acc => Nat.lor (g i) acc) (Nat.lor (g n) 0) =
        Nat.lor (Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.lor acc (g i)) n) (g n)
      rw [show Nat.lor (g n) 0 = g n by rw [Nat.lor_eq, Nat.or_zero], hacc, ih]
  let P (n : Nat) := Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (v2N ((idRows ()).getD i V2.zero)) (128 * i))) n
  have hsame : ∀ n, n ≤ 112 → P n = rep 1 129 n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      change Nat.lor (P n) (Nat.shiftLeft (v2N ((idRows ()).getD n V2.zero)) (128 * n)) =
        Nat.lor (rep 1 129 n) (Nat.shiftLeft 1 (Nat.mul 129 n))
      rw [ih (by omega), hrow n (by omega)]
      congr 1
      simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.mul_eq, Nat.one_mul, ← Nat.pow_add]
      congr 1
      omega
  have hfinal (n : Nat) (hn : n ≤ 112) :
      (List.range n).foldr
        (fun i acc => Nat.lor (Nat.shiftLeft (v2N ((idRows ()).getD i V2.zero)) (128 * i)) acc) 0 =
        rep 1 129 n := by
    rw [hfold]
    exact hsame n hn
  rw [hone]
  unfold encR
  exact hfinal 112 (Nat.le_refl 112)

theorem wf_idRows : WfA (idRows ()) := by
  refine ⟨CFSG.Sporadic.J4.idRows_size, Array.all_eq_true.mpr ?_⟩
  intro i hi
  exact CFSG.Sporadic.J4.idRows_wf _ (Array.getElem_mem hi)

theorem v2N_frApply (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Array V2} (_hM : WfA M)
    {v : V2} (_hv : v.wf = true) : v2N (frApply (frTable M) v) = vecJ rm (v2N v) (encR M) := by
  obtain ⟨-, hrm⟩ := consts_c _hK
  subst hrm
  have hM : ∀ i (h : i < M.size), M[i].wf = true := Array.all_eq_true.mp _hM.2
  rw [fr_core, vecJ_eq]
  refine xsum_congr (fun k hk => ?_)
  rw [and_one_bit, rowJ_eq hM hk]
  split <;> simp

theorem wf_frApply {M : Array V2} (_hM : WfA M) (v : V2) : (frApply (frTable M) v).wf = true := by
  apply CFSG.Sporadic.J4.frApply_frTable_wf
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  exact (Array.all_eq_true.mp _hM.2) i hi

theorem enc_transposeRows (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2}
    (_hX : WfA X) : encR (transposeRows X) = trJ t0 t1 t2 t3 t4 t5 t6 (encR X) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := consts_t _hK
  subst e0 e1 e2 e3 e4 e5 e6
  have hX : ∀ i (h : i < X.size), X[i].wf = true := Array.all_eq_true.mp _hX.2
  apply Nat.eq_of_testBit_eq
  intro p
  rw [trJ_bit, encR_bit]
  by_cases hp : p / 128 < 128
  · rw [ite_eq_left hp, encR_bit]
    have f1 : (128 * (p % 128) + p / 128) / 128 = p % 128 := by omega
    have f2 : (128 * (p % 128) + p / 128) % 128 = p / 128 := by omega
    rw [f1, f2]
    by_cases hr : p / 128 < 112
    · have hT : (transposeRows X)[p / 128]?.getD V2.zero =
          V2.ofFn fun i => (X[i]?.getD V2.zero).testBit (p / 128) := by
        simp [transposeRows, hr]
      rw [hT, ofFn_bits, testBit_V2 _ hp]
      simp [hr]
    · rw [wf_bit (wf_getD hX _) (by omega)]
      simp [hr]
  · rw [ite_eq_right hp, encR_bit]
    have h1 : ¬ p / 128 < 112 := by omega
    simp [h1]

theorem wf_transposeRows (X : Array V2) : WfA (transposeRows X) := by
  refine ⟨?_, Array.all_eq_true.mpr ?_⟩
  · simp only [transposeRows, Array.size_ofFn]
  · intro i hi
    exact CFSG.Sporadic.J4.transposeRows_wf X _ (Array.getElem_mem hi)

private def xs (f : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k b => f k ^^ b) n

private theorem xs_succ (f : Nat → Bool) (n : Nat) : xs f (n + 1) = (f n ^^ xs f n) := rfl

private theorem xs_congr {f g : Nat → Bool} : ∀ n, (∀ k < n, f k = g k) → xs f n = xs g n
  | 0, _ => rfl
  | n + 1, h => by rw [xs_succ, xs_succ, xs_congr n fun k hk => h k (by omega), h n (by omega)]

private theorem xs_xor (f g : Nat → Bool) : ∀ n, xs (fun k => f k ^^ g k) n = (xs f n ^^ xs g n)
  | 0 => rfl
  | n + 1 => by
    rw [xs_succ, xs_succ, xs_succ, xs_xor f g n]
    cases f n <;> cases g n <;> cases xs f n <;> cases xs g n <;> rfl

private theorem xs_and_left (b : Bool) (f : Nat → Bool) : ∀ n,
    xs (fun k => b && f k) n = (b && xs f n)
  | 0 => by cases b <;> rfl
  | n + 1 => by
    rw [xs_succ, xs_succ, xs_and_left b f n]
    cases b <;> simp

private theorem xs_false : ∀ n, xs (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by rw [xs_succ, xs_false n]; rfl

private theorem xs_comm (f : Nat → Nat → Bool) (m : Nat) : ∀ n,
    xs (fun j => xs (fun k => f j k) m) n = xs (fun k => xs (fun j => f j k) n) m
  | 0 => (xs_false m).symm
  | n + 1 => by
    rw [xs_succ, xs_comm f m n, ← xs_xor]
    rfl

private theorem xs_single (a : Nat) (b : Bool) : ∀ n,
    xs (fun j => decide (j = a) && b) n = (decide (a < n) && b)
  | 0 => by simp [xs]
  | n + 1 => by
    rw [xs_succ, xs_single a b n]
    by_cases h : n = a
    · subst h
      simp
    · by_cases h' : a < n
      · have h2 : a < n + 1 := by omega
        simp [h, h', h2]
      · have h2 : ¬ a < n + 1 := by omega
        simp [h, h', h2]

private theorem testBit_xsum (f : Nat → Nat) (j : Nat) : ∀ n,
    (xsum f n).testBit j = xs (fun k => (f k).testBit j) n
  | 0 => Nat.zero_testBit j
  | n + 1 => by rw [xsum_succ, xs_succ, Nat.testBit_xor, testBit_xsum f j n, Bool.xor_comm]

private theorem xor_and (a b c : Bool) : ((a ^^ b) && c) = ((a && c) ^^ (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

private noncomputable def vm (R : Nat → Nat) (a : Nat) : Nat :=
  xsum (fun k => if a.testBit k then R k else 0) 112

private def dot (a v : Nat) : Bool := xs (fun j => a.testBit j && v.testBit j) 112

private noncomputable def ofBits (g : Nat → Bool) : Nat := xsum (fun k => if g k then 2 ^ k else 0) 112

private noncomputable def colv (R : Nat → Nat) (u : Nat) : Nat := ofBits fun k => dot (R k) u

private noncomputable def rowN (X : Array V2) (k : Nat) : Nat := v2N (X[k]?.getD V2.zero)

private theorem testBit_vm (R : Nat → Nat) (a j : Nat) :
    (vm R a).testBit j = xs (fun k => a.testBit k && (R k).testBit j) 112 := by
  rw [vm, testBit_xsum]
  exact xs_congr 112 fun k _ => by cases a.testBit k <;> simp

private theorem testBit_ofBits (g : Nat → Bool) (k : Nat) :
    (ofBits g).testBit k = (decide (k < 112) && g k) := by
  rw [ofBits, testBit_xsum]
  have h : ∀ i < 112, ((if g i then 2 ^ i else 0 : Nat)).testBit k = (decide (i = k) && g k) := by
    intro i _
    by_cases e : i = k
    · subst e
      cases g i <;> simp [Nat.testBit_two_pow_self]
    · cases g i <;> simp [e]
  rw [xs_congr 112 h, xs_single]

private theorem ofBits_lt (g : Nat → Bool) : ofBits g < 2 ^ 112 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by
    rw [testBit_ofBits]
    simp [Nat.not_lt.2 hk]

private theorem vm_xor (R : Nat → Nat) (a b : Nat) : vm R (a ^^^ b) = vm R a ^^^ vm R b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_vm, testBit_vm, testBit_vm, ← xs_xor]
  exact xs_congr 112 fun k _ => by rw [Nat.testBit_xor, xor_and]

private theorem dot_xor (a b v : Nat) : dot (a ^^^ b) v = (dot a v ^^ dot b v) := by
  rw [dot, dot, dot, ← xs_xor]
  exact xs_congr 112 fun k _ => by rw [Nat.testBit_xor, xor_and]

private theorem vm_one (R : Nat → Nat) {r : Nat} (hr : r < 112) : vm R (2 ^ r) = R r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm]
  have h : ∀ k < 112, ((2 ^ r : Nat).testBit k && (R k).testBit j) =
      (decide (k = r) && (R r).testBit j) := by
    intro k _
    rw [Nat.testBit_two_pow]
    by_cases e : k = r
    · subst e
      simp
    · simp [e, Ne.symm e]
  rw [xs_congr 112 h, xs_single]
  simp [hr]

private theorem dot_vm (R : Nat → Nat) (a u : Nat) : dot (vm R a) u = dot a (colv R u) := by
  rw [dot, dot]
  have h1 : ∀ j, ((vm R a).testBit j && u.testBit j) =
      xs (fun k => a.testBit k && ((R k).testBit j && u.testBit j)) 112 := by
    intro j
    rw [testBit_vm, Bool.and_comm, ← xs_and_left]
    exact xs_congr 112 fun k _ => by cases a.testBit k <;> cases u.testBit j <;> simp
  rw [xs_congr 112 fun j _ => h1 j, xs_comm]
  refine xs_congr 112 fun k hk => ?_
  rw [xs_and_left, colv, testBit_ofBits]
  simp [hk, dot]

private theorem dot_one {k : Nat} (hk : k < 112) (v : Nat) : dot (2 ^ k) v = v.testBit k := by
  rw [dot]
  have h : ∀ j < 112, ((2 ^ k : Nat).testBit j && v.testBit j) = (decide (j = k) && v.testBit k) := by
    intro j _
    rw [Nat.testBit_two_pow]
    by_cases e : j = k
    · subst e
      simp
    · simp [e, Ne.symm e]
  rw [xs_congr 112 h, xs_single]
  simp [hk]

private theorem vm_assoc (R S : Nat → Nat) (a : Nat) :
    vm S (vm R a) = vm (fun k => vm S (R k)) a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm, testBit_vm]
  have h1 : ∀ l, ((vm R a).testBit l && (S l).testBit j) =
      xs (fun k => a.testBit k && ((R k).testBit l && (S l).testBit j)) 112 := by
    intro l
    rw [testBit_vm, Bool.and_comm, ← xs_and_left]
    exact xs_congr 112 fun k _ => by cases a.testBit k <;> cases (S l).testBit j <;> simp
  rw [xs_congr 112 fun l _ => h1 l, xs_comm]
  refine xs_congr 112 fun k _ => ?_
  rw [xs_and_left, testBit_vm]

private theorem vm_id {a : Nat} (ha : a < 2 ^ 112) : vm (fun k => 2 ^ k) a = a := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_vm]
  by_cases hj : j < 112
  · have h : ∀ k < 112, (a.testBit k && (2 ^ k : Nat).testBit j) =
        (decide (k = j) && a.testBit j) := by
      intro k _
      rw [Nat.testBit_two_pow]
      by_cases e : k = j
      · subst e
        simp
      · simp [e]
    rw [xs_congr 112 h, xs_single]
    simp [hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega)))]
    refine (xs_congr 112 fun k hk => ?_).trans (xs_false 112)
    rw [Nat.testBit_two_pow]
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega

private theorem vm_congr {R R' : Nat → Nat} (h : ∀ k < 112, R k = R' k) (a : Nat) :
    vm R a = vm R' a :=
  xsum_congr fun k hk => by rw [h k hk]

private theorem colv_inj {R S : Nat → Nat} (h : ∀ k < 112, vm S (R k) = 2 ^ k) :
    ∀ u < 2 ^ 112, colv R u = 0 → u = 0 := by
  have hsurj : ∀ v < 2 ^ 112, colv R (colv S v) = v := by
    intro v hv
    apply Nat.eq_of_testBit_eq
    intro k
    rw [colv, testBit_ofBits]
    by_cases hk : k < 112
    · rw [← dot_vm, h k hk, dot_one hk]
      simp [hk]
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [hk]
  let f : Fin (2 ^ 112) → Fin (2 ^ 112) := fun u => ⟨colv R u.val, ofBits_lt _⟩
  have hf : Function.Surjective f := fun v => ⟨⟨colv S v.val, ofBits_lt _⟩, Fin.ext (by
    dsimp only [f]
    exact hsurj v.val v.isLt)⟩
  have hinj := Finite.injective_iff_surjective.2 hf
  have h0 : colv R 0 = 0 := Nat.eq_of_testBit_eq fun k => by
    rw [colv, testBit_ofBits, Nat.zero_testBit, dot]
    rw [xs_congr 112 fun j _ => by rw [Nat.zero_testBit, Bool.and_false], xs_false]
    simp
  intro u hu hzero
  have := @hinj ⟨u, hu⟩ ⟨0, Nat.two_pow_pos 112⟩ (Fin.ext (by simp [f, hzero, h0]))
  exact congrArg Fin.val this

private def pivotOf (m : Array V2) (c : Nat) : Nat :=
  (List.range' c (112 - c)).foldl (fun p i => if (p == 112 && (m[i]!).testBit c) = true then i else p)
    112

private def elimRow (c : Nat) (mc rc : V2) (s : Array V2 × Array V2) (i : Nat) :
    Array V2 × Array V2 :=
  if (i != c && (s.1[i]!).testBit c) = true then
    (s.1.set! i ((s.1[i]!).xor mc), s.2.set! i ((s.2[i]!).xor rc))
  else s

private def stepCol (s : Array V2 × Array V2) (c : Nat) : Array V2 × Array V2 :=
  if pivotOf s.1 c < 112 then
    (List.range' 0 112).foldl (fun t i => elimRow c s.1[pivotOf s.1 c]! s.2[pivotOf s.1 c]! t i)
      ((s.1.set! (pivotOf s.1 c) s.1[c]!).set! c s.1[pivotOf s.1 c]!,
        (s.2.set! (pivotOf s.1 c) s.2[c]!).set! c s.2[pivotOf s.1 c]!)
  else s

private theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

private theorem invRows_eq_run (X : Array V2) :
    invRows X = Id.run (pure ((List.range' 0 112).foldl (fun s c => stepCol s c) (X, idRows ())).2) := by
  simp only [invRows, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind,
    Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero, Prod.mk.eta, stepCol, elimRow, pivotOf]
  rfl

private theorem run_pure_eq {α : Type} (a : α) : Id.run (pure a : Id α) = a := rfl

private theorem eta_stepCol : (fun s c => stepCol s c) = stepCol := rfl

private theorem invRows_eq_model (X : Array V2) :
    invRows X = ((List.range' 0 112).foldl stepCol (X, idRows ())).2 := by
  rw [invRows_eq_run, run_pure_eq, eta_stepCol]

private theorem get!_getD (M : Array V2) (i : Nat) : M[i]! = M[i]?.getD V2.zero := by
  by_cases h : i < M.size
  · rw [getElem!_pos M i h, getElem?_pos M i h, Option.getD_some]
  · rw [getElem!_neg M i h, getElem?_neg M i h, Option.getD_none]
    rfl

private theorem get_set {M : Array V2} (hM : M.size = 112) {i j : Nat} (hj : j < 112) (v : V2) :
    (M.set! i v)[j]! = if i = j then v else M[j]! := by
  have hj' : j < M.size := by omega
  rw [Array.set!_eq_setIfInBounds, getElem!_pos (M.setIfInBounds i v) j (by simp [hj']),
    Array.getElem_setIfInBounds hj', getElem!_pos M j hj']

private theorem size_set (M : Array V2) (i : Nat) (v : V2) : (M.set! i v).size = M.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem v2N_lt112 {v : V2} (hv : v.wf = true) : v2N v < 2 ^ 112 :=
  Nat.lt_pow_two_of_testBit _ fun _ hk => wf_bit hv hk

theorem id_row {i : Nat} (hi : i < 112) : v2N ((idRows ())[i]?.getD V2.zero) = 2 ^ i := by
  have hg : (idRows ())[i]?.getD V2.zero = V2.ofFn fun j => j == i := by
    simp [idRows, hi]
  apply Nat.eq_of_testBit_eq
  intro k
  rw [hg, ofFn_bits, Nat.testBit_two_pow]
  by_cases e : k = i
  · subst e
    simp [hi]
  · simp [e, Ne.symm e]

private def Good (X : Array V2) (s : Array V2 × Array V2) : Prop :=
  s.1.size = 112 ∧ s.2.size = 112 ∧
    (∀ i < 112, (s.1[i]!).wf = true ∧ (s.2[i]!).wf = true ∧
      v2N s.1[i]! = vm (rowN X) (v2N s.2[i]!)) ∧
    ∀ v < 2 ^ 112, (∀ i < 112, dot (v2N s.2[i]!) v = false) → v = 0

private def Col (m : Array V2) (c : Nat) : Prop :=
  ∀ c' < c, ∀ i < 112, (v2N m[i]!).testBit c' = decide (i = c')

private theorem good_xor {X : Array V2} {s : Array V2 × Array V2} (hG : Good X s) {r c : Nat}
    (hr : r < 112) (hc : c < 112) (hrc : r ≠ c) :
    Good X (s.1.set! r ((s.1[r]!).xor s.1[c]!), s.2.set! r ((s.2[r]!).xor s.2[c]!)) := by
  obtain ⟨hs1, hs2, hrow, hinj⟩ := hG
  refine ⟨by rw [size_set, hs1], by rw [size_set, hs2], fun t ht => ?_,
    fun v hv h => hinj v hv fun t ht => ?_⟩
  · dsimp only
    rw [get_set hs1 ht, get_set hs2 ht]
    by_cases e : r = t
    · rw [ite_eq_left e, ite_eq_left e]
      obtain ⟨a1, b1, l1⟩ := hrow r hr
      obtain ⟨a2, b2, l2⟩ := hrow c hc
      exact ⟨wf_xor a1 a2, wf_xor b1 b2, by rw [v2N_xor, v2N_xor, l1, l2, vm_xor]⟩
    · rw [ite_eq_right e, ite_eq_right e]
      exact hrow t ht
  · have hcs := h c hc
    dsimp only at hcs
    rw [get_set hs2 hc, ite_eq_right hrc] at hcs
    by_cases e : t = r
    · subst e
      have := h t ht
      dsimp only at this
      rw [get_set hs2 ht, ite_eq_left rfl, v2N_xor, dot_xor, hcs] at this
      simpa using this
    · have := h t ht
      dsimp only at this
      rwa [get_set hs2 ht, ite_eq_right (Ne.symm e)] at this

private theorem good_swap {X : Array V2} {s : Array V2 × Array V2} (hG : Good X s) {p c : Nat}
    (hp : p < 112) (hc : c < 112) :
    Good X ((s.1.set! p s.1[c]!).set! c s.1[p]!, (s.2.set! p s.2[c]!).set! c s.2[p]!) := by
  obtain ⟨hs1, hs2, hrow, hinj⟩ := hG
  have ht1 : (s.1.set! p s.1[c]!).size = 112 := by rw [size_set, hs1]
  have ht2 : (s.2.set! p s.2[c]!).size = 112 := by rw [size_set, hs2]
  have hget : ∀ (M : Array V2), M.size = 112 → ∀ t < 112, ((M.set! p M[c]!).set! c M[p]!)[t]! =
      if c = t then M[p]! else if p = t then M[c]! else M[t]! := fun M hM t ht => by
    have hM1 : (M.set! p M[c]!).size = 112 := by rw [size_set, hM]
    rw [get_set hM1 ht, get_set hM ht]
  refine ⟨by rw [size_set, ht1], by rw [size_set, ht2], fun t ht => ?_,
    fun v hv h => hinj v hv fun t ht => ?_⟩
  · dsimp only
    rw [hget s.1 hs1 t ht, hget s.2 hs2 t ht]
    by_cases e1 : c = t
    · rw [ite_eq_left e1, ite_eq_left e1]
      exact hrow p hp
    · rw [ite_eq_right e1, ite_eq_right e1]
      by_cases e2 : p = t
      · rw [ite_eq_left e2, ite_eq_left e2]
        exact hrow c hc
      · rw [ite_eq_right e2, ite_eq_right e2]
        exact hrow t ht
  · by_cases htp : t = p
    · subst htp
      have := h c hc
      dsimp only at this
      rwa [hget s.2 hs2 c hc, ite_eq_left rfl] at this
    · by_cases htc : t = c
      · subst htc
        have := h p hp
        dsimp only at this
        rwa [hget s.2 hs2 p hp, ite_eq_right htp, ite_eq_left rfl] at this
      · have := h t ht
        dsimp only at this
        rwa [hget s.2 hs2 t ht, ite_eq_right (Ne.symm htc), ite_eq_right (Ne.symm htp)] at this

private theorem pivot_spec (M : Array V2) (c : Nat) :
    (pivotOf M c < 112 → c ≤ pivotOf M c ∧ (M[pivotOf M c]!).testBit c = true) ∧
      (¬ pivotOf M c < 112 → ∀ r, c ≤ r → r < 112 → (M[r]!).testBit c = false) := by
  have key : ∀ (L : List Nat) (q : Nat),
      (q = 112 ∨ (c ≤ q ∧ q < 112 ∧ (M[q]!).testBit c = true)) → (∀ x ∈ L, c ≤ x ∧ x < 112) →
      ((L.foldl (fun p r => if (p == 112 && (M[r]!).testBit c) = true then r else p) q = 112 ∨
        (c ≤ L.foldl (fun p r => if (p == 112 && (M[r]!).testBit c) = true then r else p) q ∧
          L.foldl (fun p r => if (p == 112 && (M[r]!).testBit c) = true then r else p) q < 112 ∧
          (M[L.foldl (fun p r => if (p == 112 && (M[r]!).testBit c) = true then r else p)
            q]!).testBit c = true)) ∧
        (L.foldl (fun p r => if (p == 112 && (M[r]!).testBit c) = true then r else p) q = 112 →
          q = 112 ∧ ∀ x ∈ L, (M[x]!).testBit c = false)) := by
    intro L
    induction L with
    | nil => intro q hq _; exact ⟨hq, fun h => ⟨h, fun _ hx => absurd hx List.not_mem_nil⟩⟩
    | cons x L ih =>
      intro q hq hL
      rw [List.foldl_cons]
      have hx := hL x List.mem_cons_self
      have hL' : ∀ y ∈ L, c ≤ y ∧ y < 112 := fun y hy => hL y (List.mem_cons_of_mem _ hy)
      by_cases hb : (q == 112 && (M[x]!).testBit c) = true
      · rw [ite_eq_left hb]
        have hb' := Bool.and_eq_true_iff.1 hb
        obtain ⟨h1, h2⟩ := ih x (Or.inr ⟨hx.1, hx.2, hb'.2⟩) hL'
        refine ⟨h1, fun h => ?_⟩
        have := (h2 h).1
        omega
      · rw [ite_eq_right hb]
        obtain ⟨h1, h2⟩ := ih q hq hL'
        refine ⟨h1, fun h => ⟨(h2 h).1, fun y hy => ?_⟩⟩
        rcases List.mem_cons.1 hy with rfl | hy'
        · have hq112 := (h2 h).1
          subst hq112
          simpa using hb
        · exact (h2 h).2 y hy'
  have hL : ∀ x ∈ List.range' c (112 - c), c ≤ x ∧ x < 112 := fun x hx => by
    rw [List.mem_range'_1] at hx
    omega
  obtain ⟨h1, h2⟩ := key (List.range' c (112 - c)) 112 (Or.inl rfl) hL
  refine ⟨fun hp => ?_, fun hp r hr1 hr2 => ?_⟩
  · rcases h1 with h | h
    · rw [pivotOf] at hp
      omega
    · exact ⟨h.1, h.2.2⟩
  · have h112 : pivotOf M c = 112 := by
      rcases h1 with h | h
      · exact h
      · exact absurd h.2.1 hp
    exact (h2 h112).2 r (by rw [List.mem_range'_1]; omega)

private theorem elim_spec {X : Array V2} {c : Nat} {mc rc : V2} (hc : c < 112)
    (hmc : (v2N mc).testBit c = true) (hrl : ∀ c' < c, (v2N mc).testBit c' = false) :
    ∀ n ≤ 112, ∀ s : Array V2 × Array V2, Good X s → s.1[c]! = mc → s.2[c]! = rc → Col s.1 c →
      Good X ((List.range' 0 n).foldl (elimRow c mc rc) s) ∧
      ((List.range' 0 n).foldl (elimRow c mc rc) s).1[c]! = mc ∧
      ((List.range' 0 n).foldl (elimRow c mc rc) s).2[c]! = rc ∧
      Col ((List.range' 0 n).foldl (elimRow c mc rc) s).1 c ∧
      ∀ r < n, r ≠ c →
        (v2N ((List.range' 0 n).foldl (elimRow c mc rc) s).1[r]!).testBit c = false := by
  intro n
  induction n with
  | zero =>
    intro _ s hG h1 h2 hC
    exact ⟨hG, h1, h2, hC, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ n ih =>
    intro hn s hG h1 h2 hC
    obtain ⟨hG1, hc1, hd1, hC1, hz1⟩ := ih (by omega) s hG h1 h2 hC
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    generalize (List.range' 0 n).foldl (elimRow c mc rc) s = t at hG1 hc1 hd1 hC1 hz1
    have hs1 := hG1.1
    have hs2 := hG1.2.1
    have hn112 : n < 112 := by omega
    have hbit : (t.1[n]!).testBit c = (v2N t.1[n]!).testBit c := testBit_V2 _ (by omega)
    rw [elimRow]
    by_cases hb : (n != c && (t.1[n]!).testBit c) = true
    · rw [ite_eq_left hb]
      have hb' := Bool.and_eq_true_iff.1 hb
      have hnc : n ≠ c := by simpa using hb'.1
      have hbn : (v2N t.1[n]!).testBit c = true := by rw [← hbit]; exact hb'.2
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := good_xor hG1 hn112 hc hnc
        rwa [hc1, hd1] at this
      · dsimp only
        rw [get_set hs1 hc, ite_eq_right hnc, hc1]
      · dsimp only
        rw [get_set hs2 hc, ite_eq_right hnc, hd1]
      · intro c' hc' r hr
        dsimp only
        rw [get_set hs1 hr]
        by_cases e : n = r
        · subst e
          rw [ite_eq_left rfl, v2N_xor, Nat.testBit_xor, hC1 c' hc' n hr, hrl c' hc', Bool.xor_false]
        · rw [ite_eq_right e]
          exact hC1 c' hc' r hr
      · intro r hr hrc'
        dsimp only
        by_cases hrn : r = n
        · subst hrn
          rw [get_set hs1 hn112, ite_eq_left rfl, v2N_xor, Nat.testBit_xor, hbn, hmc]
          rfl
        · rw [get_set hs1 (by omega), ite_eq_right (Ne.symm hrn)]
          exact hz1 r (by omega) hrc'
    · rw [ite_eq_right hb]
      refine ⟨hG1, hc1, hd1, hC1, fun r hr hrc' => ?_⟩
      by_cases hrn : r = n
      · subst hrn
        rw [← hbit]
        simpa [hrc'] using hb
      · exact hz1 r (by omega) hrc'

private theorem no_pivot_false {X : Array V2}
    (hXinj : ∀ u < 2 ^ 112, colv (rowN X) u = 0 → u = 0) {s : Array V2 × Array V2}
    (hG : Good X s) {c : Nat} (hc : c < 112) (hC : Col s.1 c)
    (hn : ∀ r, c ≤ r → r < 112 → (v2N s.1[r]!).testBit c = false) : False := by
  obtain ⟨_, _, hrow, hinj⟩ := hG
  let g : Nat → Bool := fun k => decide (k = c) || (decide (k < c) && (v2N s.1[k]!).testBit c)
  have hu : ∀ k, (ofBits g).testBit k = (decide (k < 112) && g k) := testBit_ofBits g
  have hdot : ∀ r < 112, dot (v2N s.2[r]!) (colv (rowN X) (ofBits g)) = false := by
    intro r hr
    rw [← dot_vm, ← (hrow r hr).2.2, dot]
    have hj : ∀ j < 112, ((v2N s.1[r]!).testBit j && (ofBits g).testBit j) =
        ((decide (j = c) && (v2N s.1[r]!).testBit c) ^^
          (decide (j = r) && (decide (r < c) && (v2N s.1[r]!).testBit c))) := by
      intro j hj
      rw [hu]
      simp only [hj, decide_true, Bool.true_and, g]
      by_cases hjc : j = c
      · subst hjc
        have : ¬ (j = r ∧ r < j) := by omega
        by_cases hjr : j = r
        · subst hjr
          simp
        · simp [hjr]
      · by_cases hjc' : j < c
        · rw [hC j hjc' r hr]
          by_cases hjr : j = r
          · subst hjr
            simp [hjc, hjc']
          · simp [hjc, Ne.symm hjr, hjr]
        · simp only [hjc, hjc', decide_false, Bool.false_or, Bool.false_and, Bool.and_false,
            Bool.false_xor]
          by_cases hjr' : j = r
          · subst hjr'
            simp [hjc']
          · simp [hjr']
    rw [xs_congr 112 hj, xs_xor, xs_single, xs_single]
    by_cases hrc : r < c
    · simp [hc, hr, hrc]
    · rw [hn r (by omega) hr]
      simp
  have h0 := hXinj (ofBits g) (ofBits_lt g) (hinj _ (ofBits_lt _) hdot)
  have := hu c
  rw [h0, Nat.zero_testBit] at this
  simp [hc, g] at this

private theorem wfA_get {X : Array V2} (hX : WfA X) {i : Nat} (hi : i < 112) : (X[i]!).wf = true := by
  have hs : i < X.size := by rw [hX.1]; exact hi
  rw [getElem!_pos X i hs]
  exact Array.all_eq_true.mp hX.2 i hs

private theorem good_start {X : Array V2} (hX : WfA X) : Good X (X, idRows ()) := by
  have hI : ∀ i < 112, v2N (idRows ())[i]! = 2 ^ i := fun i hi => by rw [get!_getD, id_row hi]
  refine ⟨hX.1, by simp [idRows], fun i hi => ⟨wfA_get hX hi, wfA_get wf_idRows hi, ?_⟩,
    fun v hv h => ?_⟩
  · dsimp only
    rw [hI i hi, vm_one _ hi, rowN, get!_getD]
  · apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.zero_testBit]
    by_cases hk : k < 112
    · have := h k hk
      dsimp only at this
      rwa [hI k hk, dot_one hk] at this
    · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem col_zero (m : Array V2) : Col m 0 := fun _ h => absurd h (Nat.not_lt_zero _)

private theorem step_spec {X : Array V2} (hXinj : ∀ u < 2 ^ 112, colv (rowN X) u = 0 → u = 0)
    {s : Array V2 × Array V2} (hG : Good X s) {c : Nat} (hc : c < 112) (hC : Col s.1 c) :
    Good X (stepCol s c) ∧ Col (stepCol s c).1 (c + 1) := by
  obtain ⟨hp1, hp2⟩ := pivot_spec s.1 c
  rw [stepCol]
  by_cases hp : pivotOf s.1 c < 112
  · rw [ite_eq_left hp]
    obtain ⟨hcp, hbit⟩ := hp1 hp
    generalize pivotOf s.1 c = p at hp hcp hbit
    have hs1 := hG.1
    have hs2 := hG.2.1
    have hbit' : (v2N s.1[p]!).testBit c = true := by rw [← testBit_V2 _ (by omega)]; exact hbit
    have hget : ∀ (M : Array V2), M.size = 112 → ∀ t < 112, ((M.set! p M[c]!).set! c M[p]!)[t]! =
        if c = t then M[p]! else if p = t then M[c]! else M[t]! := fun M hM t ht => by
      have hM1 : (M.set! p M[c]!).size = 112 := by rw [size_set, hM]
      rw [get_set hM1 ht, get_set hM ht]
    have hrl : ∀ c' < c, (v2N s.1[p]!).testBit c' = false := fun c' hc' => by
      rw [hC c' hc' p hp]
      simp only [decide_eq_false_iff_not]
      omega
    have hC1 : Col ((s.1.set! p s.1[c]!).set! c s.1[p]!) c := by
      intro c' hc' r hr
      rw [hget s.1 hs1 r hr]
      by_cases e1 : c = r
      · rw [ite_eq_left e1, hrl c' hc']
        simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega
      · rw [ite_eq_right e1]
        by_cases e2 : p = r
        · rw [ite_eq_left e2, hC c' hc' c hc]
          simp only [decide_eq_decide]
          omega
        · rw [ite_eq_right e2]
          exact hC c' hc' r hr
    obtain ⟨hG2, hc2, _, hC2, hz2⟩ := elim_spec (rc := s.2[p]!) hc hbit' hrl 112 le_rfl _
      (good_swap hG hp hc) (by dsimp only; rw [hget s.1 hs1 c hc, ite_eq_left rfl])
      (by dsimp only; rw [hget s.2 hs2 c hc, ite_eq_left rfl]) hC1
    refine ⟨hG2, fun c' hc' r hr => ?_⟩
    by_cases hcc : c' = c
    · subst hcc
      by_cases hrc : r = c'
      · subst hrc
        rw [hc2, hbit']
        simp
      · rw [hz2 r hr hrc]
        simp [hrc]
    · exact hC2 c' (by omega) r hr
  · exact (no_pivot_false hXinj hG hc hC fun r h1 h2 => by
      rw [← testBit_V2 _ (by omega)]
      exact hp2 hp r h1 h2).elim

private theorem fold_spec {X : Array V2} (hX : WfA X)
    (hXinj : ∀ u < 2 ^ 112, colv (rowN X) u = 0 → u = 0) : ∀ n ≤ 112,
    Good X ((List.range' 0 n).foldl stepCol (X, idRows ())) ∧
      Col ((List.range' 0 n).foldl stepCol (X, idRows ())).1 n := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨good_start hX, col_zero _⟩
  | succ n ih =>
    intro hn
    obtain ⟨hG, hC⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add,
      Nat.one_mul]
    exact step_spec hXinj hG (by omega) hC

def ofN (x : Nat) : V2 := ⟨UInt64.ofNat x, UInt64.ofNat (x >>> 64)⟩

theorem ofN_bits (x k : Nat) :
    (v2N (ofN x)).testBit k = (decide (k < 128) && x.testBit k) := by
  rw [v2N_testBit]
  change (if k < 64 then (UInt64.ofNat x).toNat.testBit k
    else (UInt64.ofNat (x >>> 64)).toNat.testBit (k - 64)) = _
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h : k < 64
  · have h2 : k < 128 := by omega
    simp [h, h2]
  · by_cases h2 : k < 128
    · have e : 64 + (k - 64) = k := by omega
      have h3 : k - 64 < 64 := by omega
      simp [h, h2, e, h3]
    · have h3 : ¬ k - 64 < 64 := by omega
      simp [h, h2, h3]

theorem ofN_eq {x : Nat} (hx : x < 2 ^ 112) : v2N (ofN x) = x := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [ofN_bits]
  by_cases hk : k < 128
  · simp [hk]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp

theorem wf_ofN {x : Nat} (hx : x < 2 ^ 112) : (ofN x).wf = true :=
  wf_of_bits fun k hk => by
    rw [ofN_eq hx]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hk))

private theorem rowJ_lt (n k : Nat) : rowJ (2 ^ 112 - 1) n k < 2 ^ 112 :=
  Nat.and_lt_two_pow _ (by omega : 2 ^ 112 - 1 < 2 ^ 112)

noncomputable def decN (n : Nat) : Array V2 :=
  Array.ofFn (n := 112) fun k => ofN (rowJ (2 ^ 112 - 1) n k.val)

theorem decN_row (n : Nat) {k : Nat} (hk : k < 112) :
    (decN n)[k]?.getD V2.zero = ofN (rowJ (2 ^ 112 - 1) n k) := by
  simp [decN, hk]

private theorem wf_decN (n : Nat) : WfA (decN n) := by
  refine ⟨by simp [decN], Array.all_eq_true.mpr fun i hi => ?_⟩
  simp only [decN, Array.getElem_ofFn]
  exact wf_of_bits fun k hk => by
    rw [ofN_eq (rowJ_lt _ _)]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowJ_lt _ _) (Nat.pow_le_pow_right (by omega) hk))

theorem consts_pad {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (h : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) : pad = padMask := by
  unfold Consts constsOK at h
  obtain ⟨-, h⟩ := andB_true h
  obtain ⟨h, -⟩ := andB_true h
  exact Nat.eq_of_beq_eq_true h

private theorem rep_bits128 {x : Nat} (hx : x < 2 ^ 128) (p : Nat) : ∀ m,
    (rep x 128 m).testBit p = (decide (p / 128 < m) && x.testBit (p % 128))
  | 0 => by simp [rep]
  | m + 1 => by
    have e : rep x 128 (m + 1) = rep x 128 m ||| x <<< (128 * m) := rfl
    rw [e, Nat.testBit_or, rep_bits128 hx p m, shl_row_bit hx m p]
    by_cases h : p / 128 = m
    · simp [h]
    · have h2 : p / 128 < m + 1 ↔ p / 128 < m := by omega
      simp [h, h2]

private theorem padMask_bit (p : Nat) :
    padMask.testBit p = (decide (p / 128 < 112) && decide (112 ≤ p % 128)) := by
  have e : Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 128)) (Nat.shiftLeft (nat_lit 1) (nat_lit 112)) =
      (2 ^ 16 - 1) <<< 112 := by decide
  have hlt : (2 ^ 16 - 1) <<< 112 < 2 ^ 128 := by decide
  unfold padMask
  rw [e, rep_bits128 hlt, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  have hm : p % 128 < 128 := Nat.mod_lt _ (by omega)
  by_cases h : 112 ≤ p % 128
  · have h2 : p % 128 - 112 < 16 := by omega
    simp [h, h2]
  · simp [h]

private theorem blt_bit {n k p : Nat} (h : Nat.blt n (Nat.shiftLeft 1 k) = true) (hp : k ≤ p) :
    n.testBit p = false := by
  have hlt : n < 1 <<< k := Eq.mp Nat.blt_eq h
  rw [Nat.one_shiftLeft] at hlt
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hp))

private theorem canon_bits {pad n : Nat} (hpad : pad = padMask) (hn : canonJ pad n = true) {p : Nat}
    (hb : n.testBit p = true) : p / 128 < 112 ∧ p % 128 < 112 := by
  unfold canonJ at hn
  obtain ⟨h1, h2⟩ := andB_true hn
  have hz : n &&& pad = 0 := Nat.eq_of_beq_eq_true h2
  have hq : p / 128 < 112 := by
    by_contra hc
    rw [blt_bit h1 (by omega : 14336 ≤ p)] at hb
    exact Bool.false_ne_true hb
  refine ⟨hq, ?_⟩
  by_contra hc
  have := congrArg (fun x => x.testBit p) hz
  simp only [Nat.testBit_and, hb, hpad, padMask_bit, Nat.zero_testBit] at this
  simp [hq] at this
  omega

theorem encR_decN {pad n : Nat} (hpad : pad = padMask) (hn : canonJ pad n = true) :
    encR (decN n) = n := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encR_bit]
  by_cases hp : p / 128 < 112
  · rw [decN_row n hp, ofN_eq (rowJ_lt _ _)]
    change (decide (p / 128 < 112) &&
      ((n >>> (p / 128 * 128)) &&& (2 ^ 112 - 1)).testBit (p % 128)) = n.testBit p
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    have e : p / 128 * 128 + p % 128 = p := by omega
    rw [e]
    by_cases hq : p % 128 < 112
    · simp [hp, hq]
    · cases hb : n.testBit p
      · simp
      · exact absurd (canon_bits hpad hn hb).2 hq
  · cases hb : n.testBit p
    · simp [hp]
    · exact absurd (canon_bits hpad hn hb).1 hp

theorem rows_of_encR_eq {A B : Array V2} (h : encR A = encR B) {i : Nat} (hi : i < 112) :
    v2N (A[i]?.getD V2.zero) = v2N (B[i]?.getD V2.zero) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 128
  · have hx := encR_fld A i j hj
    rw [h, encR_fld B i j hj] at hx
    dsimp only at hx
    rw [ite_eq_left hi, ite_eq_left hi] at hx
    exact hx.symm
  · have hj' : 128 ≤ j := by omega
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt _) (Nat.pow_le_pow_right (by omega) hj')),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt _) (Nat.pow_le_pow_right (by omega) hj'))]

private theorem mul_rows (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2} (hX : WfA X)
    {n : Nat} (hn : canonJ pad n = true) (h : Nat.beq (mulJ c rm (encR X) n) one = true) :
    ∀ k < 112, vm (rowN (decN n)) (rowN X k) = 2 ^ k := by
  have e1 : encR (mulRows X (decN n)) = encR (idRows ()) := by
    rw [enc_mulRows hK hX (wf_decN n), encR_decN (consts_pad hK) hn, enc_idRows hK]
    exact Nat.eq_of_beq_eq_true h
  intro k hk
  have := rows_of_encR_eq e1 hk
  have hs : k < X.size := by rw [hX.1]; exact hk
  have hm : (mulRows X (decN n))[k]?.getD V2.zero = frApply (frTable (decN n)) (X[k]?.getD V2.zero) := by
    simp [mulRows, hs]
  rw [hm, fr_core, id_row hk] at this
  exact this

theorem invRows_enc (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array V2} (_hX : WfA X)
    {n : Nat} (_hn : canonJ pad n = true) (_h : Nat.beq (mulJ c rm (encR X) n) one = true) :
    WfA (invRows X) ∧ encR (invRows X) = n := by
  have hmul := mul_rows _hK _hX _hn _h
  rw [invRows_eq_model]
  obtain ⟨⟨_, hs2, hrow, _⟩, hC⟩ := fold_spec _hX (colv_inj hmul) 112 le_rfl
  generalize (List.range' 0 112).foldl stepCol (X, idRows ()) = s at hs2 hrow hC
  have hr : ∀ i < 112, v2N s.2[i]! = rowN (decN n) i := by
    intro i hi
    obtain ⟨hw1, hw2, hl⟩ := hrow i hi
    have hlo : v2N s.1[i]! = 2 ^ i := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_two_pow]
      by_cases hj : j < 112
      · rw [hC j hj i hi]
      · rw [wf_bit hw1 (by omega)]
        simp only [Bool.false_eq, decide_eq_false_iff_not]
        omega
    rw [hlo] at hl
    calc v2N s.2[i]! = vm (fun k => 2 ^ k) (v2N s.2[i]!) := (vm_id (v2N_lt112 hw2)).symm
      _ = vm (fun k => vm (rowN (decN n)) (rowN X k)) (v2N s.2[i]!) :=
          vm_congr (fun k hk => (hmul k hk).symm) _
      _ = vm (rowN (decN n)) (vm (rowN X) (v2N s.2[i]!)) := (vm_assoc _ _ _).symm
      _ = vm (rowN (decN n)) (2 ^ i) := by rw [← hl]
      _ = rowN (decN n) i := vm_one _ hi
  refine ⟨⟨hs2, Array.all_eq_true.mpr fun i hi => ?_⟩, ?_⟩
  · have := (hrow i (by rw [hs2] at hi; exact hi)).2.1
    rwa [getElem!_pos s.2 i hi] at this
  · rw [← encR_decN (consts_pad _hK) _hn]
    refine fld_eq (by omega : 0 < 128) (encR_fld _) (CFSG.KS.PackFld.fld_congr (encR_fld (decN n)) ?_)
    intro i
    by_cases hi : i < 112
    · rw [ite_eq_left hi, ite_eq_left hi]
      have := hr i hi
      rw [get!_getD] at this
      exact this.symm
    · rw [ite_eq_right hi, ite_eq_right hi]

end Prim

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem wf_bool {X : Array V2} (h : WfA X) : (X.size == 112 && X.all V2.wf) = true := by
  obtain ⟨h1, h2⟩ := h
  rw [Bool.and_eq_true]
  exact ⟨beq_iff_eq.mpr h1, h2⟩

theorem beq_false {a b : Nat} (h : neN a b = true) : Nat.beq a b = false := by
  unfold neN notB at h
  cases hb : Nat.beq a b
  · rfl
  · rw [hb] at h
    exact absurd h (by decide)

section Derived

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

theorem wf_powRows {M : Array V2} (hM : WfA M) : ∀ e, WfA (powRows M e)
  | 0 => wf_idRows
  | e + 1 => wf_mulRows (wf_powRows hM e) hM

theorem enc_powRows (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {M : Array V2} (hM : WfA M) :
    ∀ e, encR (powRows M e) = powJ c rm one (encR M) e
  | 0 => by rw [powRows, enc_idRows hK]; rfl
  | e + 1 => by
    rw [powRows, enc_mulRows hK (wf_powRows hM e) hM, enc_powRows hK hM e]
    exact (strictN_eq (powJ c rm one (encR M) e) (fun a => mulJ c rm a (encR M))).symm

theorem letter_enc {mats invs : Array (Array V2)} {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k)
    (l : Int) :
    WfA (if 0 < l then mats[l.toNat - 1]?.getD (idRows ()) else invs[(-l).toNat - 1]?.getD (idRows ())) ∧
      encR (if 0 < l then mats[l.toNat - 1]?.getD (idRows ()) else invs[(-l).toNat - 1]?.getD (idRows ())) =
        letJ one ms is l := by
  rcases l with (_ | k) | k
  · simpa [letJ] using hi 0
  · have : (0 : Int) < Int.ofNat (k + 1) := Int.ofNat_lt.mpr (Nat.succ_pos k)
    simp only [this, ↓reduceIte]
    simpa [letJ] using hm k
  · have : ¬ (0 : Int) < Int.negSucc k := by omega
    simp only [this, ↓reduceIte]
    have hk : (-Int.negSucc k).toNat - 1 = k := by omega
    rw [hk]
    exact hi k

theorem enc_wordFrom (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : Array (Array V2)}
    {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k) :
    ∀ (w : List Int) (acc : Array V2), WfA acc →
      WfA (w.foldl (fun acc l => mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD (idRows ())
        else invs[(-l).toNat - 1]?.getD (idRows ()))) acc) ∧
      encR (w.foldl (fun acc l => mulRows acc (if 0 < l then mats[l.toNat - 1]?.getD (idRows ())
        else invs[(-l).toNat - 1]?.getD (idRows ()))) acc) = wordFrom c rm one ms is w (encR acc)
  | [], acc, h => ⟨h, rfl⟩
  | l :: w, acc, h => by
    obtain ⟨hl1, hl2⟩ := letter_enc hm hi l
    rw [List.foldl_cons]
    have hw := enc_wordFrom hK hm hi w _ (wf_mulRows h hl1)
    refine ⟨hw.1, ?_⟩
    rw [hw.2, enc_mulRows hK h hl1, hl2]
    exact (strictN_eq (mulJ c rm (encR acc) (letJ one ms is l)) (wordFrom c rm one ms is w)).symm

theorem enc_wordRows (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {mats invs : Array (Array V2)}
    {ms is : List Nat}
    (hm : ∀ k, WfA (mats[k]?.getD (idRows ())) ∧ encR (mats[k]?.getD (idRows ())) = getN one ms k)
    (hi : ∀ k, WfA (invs[k]?.getD (idRows ())) ∧ encR (invs[k]?.getD (idRows ())) = getN one is k)
    (w : List Int) :
    WfA (wordRows mats invs w) ∧ encR (wordRows mats invs w) = wordJ c rm one ms is w := by
  have h := enc_wordFrom hK hm hi w (idRows ()) wf_idRows
  rw [enc_idRows hK] at h
  exact h

end Derived

end CFSG.KC.J4Q

end
