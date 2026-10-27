module

public import Certificates.Data.Kernel.SporSch.HNF5
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Sporadic.HNSchreier.SeedsCheckInputs
import CFSG.Certificates.Kernel.SporSch.HNF5Lane

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native

@[expose] noncomputable def rows5 (T : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := 133) fun i => Array.ofFn (n := 133) fun j => lane5 (T i.val) j.val

@[expose] def Canon5 (T : Nat → Nat) : Prop := ∀ i < 133, canon5 (T i) = true

theorem rows5_get (T : Nat → Nat) {i j : Nat} (hi : i < 133) (hj : j < 133) :
    ((rows5 T)[i]!)[j]! = lane5 (T i) j := by
  unfold rows5
  rw [LyM.ofFn_get! _ hi, LyM.ofFn_get! _ hj]

theorem pay5_sound {R : Nat → Nat} {cs : List Char} (h : pay5K R cs = true) :
    rowsOf 5 133 (String.ofList cs) = rows5 R :=
  F5Lane.pay5_rows h

theorem mulM5_sound {X Y Z : Nat → Nat} (hX : Canon5 X) (hY : Canon5 Y)
    (h : ∀ i < 133, vm5 Y (X i) = Z i) : mulM 5 133 (rows5 X) (rows5 Y) = rows5 Z := by
  unfold mulM
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum, ← h i i.isLt, F5Lane.vm5_lane hY (hX i i.isLt) k.isLt]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun j hj => ?_)
  have hj' := Finset.mem_range.1 hj
  rw [F5Lane.col_get _ hj', rows5_get _ i.isLt hj', rows5_get _ hj' k.isLt]

theorem mulM5_idL {X : Nat → Nat} (hX : Canon5 X) : mulM 5 133 (idM 133) (rows5 X) = rows5 X := by
  unfold mulM
  conv_rhs => unfold rows5
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun k => ?_))
  unfold dot
  rw [LyM.fold_sum]
  have e : ∀ j ∈ Finset.range 133, ((idM 133)[i.val]!)[j]! * (col 133 (rows5 X) k.val)[j]! =
      if i.val = j then lane5 (X j) k.val else 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [F5Lane.idM_get i.isLt hj', F5Lane.col_get _ hj', rows5_get _ hj' k.isLt]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.2 i.isLt),
    Nat.mod_eq_of_lt (F5Lane.canon5_lane (hX i i.isLt) k.isLt)]

theorem rows5_eq_idM {T : Nat → Nat} (h : ∀ i < 133, T i = idRow5 i) : rows5 T = idM 133 := by
  unfold rows5 idM
  refine congrArg Array.ofFn (funext fun i => congrArg Array.ofFn (funext fun j => ?_))
  rw [h i i.isLt, F5Lane.lane5_idRow5]
  by_cases hij : i.val = j.val
  · rw [ite_eq_left hij.symm, ite_eq_left hij]
  · rw [ite_eq_right (Ne.symm hij), ite_eq_right hij]

theorem eqId5_sound {T : Nat → Nat} (h : ∀ i < 133, T i = idRow5 i) :
    (rows5 T == idM 133) = true := by
  rw [rows5_eq_idM h]
  exact beq_self_eq_true _

theorem notId5_sound {T : Nat → Nat} (hT : Canon5 T) (h : ∃ i < 133, T i ≠ idRow5 i) :
    notIdM 133 (rows5 T) = true := by
  obtain ⟨i, hi, hne⟩ := h
  unfold notIdM
  by_contra hb
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at hb
  apply hne
  refine F5Lane.eq_of_lanes (F5Lane.canon5_lt (hT i hi)) (F5Lane.idRow5_lt hi) fun j hj => ?_
  have h1 := hb ⟨i, hi⟩ (List.mem_finRange _)
  simp only at h1
  rw [Nat.all_eq_finRange_all, List.all_eq_true] at h1
  have h2 := h1 ⟨j, hj⟩ (List.mem_finRange _)
  simp only [beq_iff_eq] at h2
  rw [rows5_get _ hi hj, Nat.mod_eq_of_lt (F5Lane.canon5_lane (hT i hi) hj)] at h2
  rw [h2, F5Lane.lane5_idRow5]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij.symm]
  · rw [ite_eq_right hij, ite_eq_right (Ne.symm hij)]

theorem rows5_congr {f g : Nat → Nat} (h : ∀ i < 133, f i = g i) : rows5 f = rows5 g := by
  unfold rows5
  exact congrArg (fun F => Array.ofFn (n := 133) F) (funext fun i => by rw [h i i.isLt])

theorem rows_of_blocks {f : Nat → Bool} (h : ∀ b < 7, allBlk (Nat.mul 19 b) f 19 = true) :
    ∀ i < 133, f i = true := by
  intro i hi
  have hb : i / 19 < 7 := by omega
  have := allBlk_spec (h (i / 19) hb) (i % 19) (Nat.mod_lt _ (by omega))
  have e : Nat.add (Nat.mul 19 (i / 19)) (i % 19) = i := by
    rw [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod i 19
  rwa [e] at this

theorem entry_mul {MT OP L R : Nat → Nat} {k l r : Nat}
    (h : ∀ b < 7, entryOK MT OP L R k b = true) (ho : OP k = 0) (hl : L k = l) (hr : R k = r) :
    ∀ i < 133, vm5 (slice5 MT r) (slice5 MT l i) = slice5 MT k i := by
  intro i hi
  have h' : ∀ b < 7, allBlk (Nat.mul 19 b) (fun i => Nat.beq (vm5 (slice5 MT r) (slice5 MT l i))
      (slice5 MT k i)) 19 = true := by
    intro b hb
    have := h b hb
    unfold entryOK at this
    rw [hl, hr, ho, CFSG.KS.Raw.strictB_eq, CFSG.KS.Raw.strictB_eq] at this
    exact this
  exact Nat.eq_of_beq_eq_true (rows_of_blocks h' i hi)

theorem entry_copy {MT OP L R : Nat → Nat} {k l : Nat}
    (h : ∀ b < 7, entryOK MT OP L R k b = true) (ho : OP k = 1) (hl : L k = l) :
    ∀ i < 133, slice5 MT l i = slice5 MT k i := by
  intro i hi
  have h' : ∀ b < 7, allBlk (Nat.mul 19 b) (fun i => Nat.beq (slice5 MT l i) (slice5 MT k i)) 19 =
      true := by
    intro b hb
    have := h b hb
    unfold entryOK at this
    rw [hl, ho, CFSG.KS.Raw.strictB_eq, CFSG.KS.Raw.strictB_eq] at this
    exact this
  exact Nat.eq_of_beq_eq_true (rows_of_blocks h' i hi)

theorem powM5_chain {M : Nat → Nat} {P : Nat → Nat → Nat} {e : Nat} (he : 1 ≤ e) (hM : Canon5 M)
    (hP : ∀ t, 1 ≤ t → t ≤ e → Canon5 (P t)) (h1 : ∀ i < 133, P 1 i = M i)
    (hs : ∀ t, 1 ≤ t → t < e → ∀ i < 133, vm5 M (P t i) = P (t + 1) i) :
    powM 5 133 (rows5 M) e = rows5 (P e) := by
  induction e with
  | zero => omega
  | succ e ih =>
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0
      rw [powM, powM, mulM5_idL hM]
      exact rows5_congr fun i hi => (h1 i hi).symm
    · rw [powM, ih h0 (fun t a b => hP t a (by omega)) (fun t a b => hs t a (by omega))]
      exact mulM5_sound (hP e h0 (by omega)) hM (hs e h0 (by omega))

theorem wordM5_chain {Ms : Nat → Array (Array Nat)} {LT : Nat → Nat → Nat} {Q : Nat → Nat → Nat}
    {w : List Nat} (hw : 1 ≤ w.length) (hL : ∀ l ∈ w, Ms l = rows5 (LT l))
    (hLc : ∀ l ∈ w, Canon5 (LT l))
    (hQ : ∀ t, 1 ≤ t → t ≤ w.length → Canon5 (Q t)) (h1 : ∀ i < 133, Q 1 i = LT (w.headD 0) i)
    (hs : ∀ t, 1 ≤ t → t < w.length → ∀ i < 133, vm5 (LT (w.getD t 0)) (Q t i) = Q (t + 1) i) :
    wordM Ms w = rows5 (Q w.length) := by
  have key : ∀ n, 1 ≤ n → n ≤ w.length →
      (w.take n).foldl (fun P l => mulM 5 133 P (Ms l)) (idM 133) = rows5 (Q n) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        obtain ⟨a, w', rfl⟩ : ∃ a w', w = a :: w' := by
          cases w with
          | nil => simp at hw
          | cons a w' => exact ⟨a, w', rfl⟩
        simp only [List.take, List.foldl, hL a List.mem_cons_self,
          mulM5_idL (hLc a List.mem_cons_self)]
        exact rows5_congr fun i hi => (h1 i hi).symm
      · have hlt : n < w.length := by omega
        rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some, List.foldl_append,
          ih h0 (by omega), List.foldl_cons, List.foldl_nil, hL _ (List.getElem_mem hlt)]
        have hg : w[n] = w.getD n 0 := by simp [List.getD_eq_getElem?_getD, hlt]
        have hc := hLc _ (List.getElem_mem hlt)
        rw [hg] at hc ⊢
        exact mulM5_sound (hQ n h0 (by omega)) hc (hs n h0 hlt)
  have := key w.length hw (Nat.le_refl _)
  rwa [List.take_length] at this

end CFSG.KS.SporSch

end
