module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqData
public import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_zero eq_xorBits xorBits_lt)

theorem xorBits_congr_bits {n : ℕ} {f g : ℕ → ℕ} {v : ℕ}
    (h : ∀ j, j < n → v.testBit j = true → f j = g j) : xorBits n f v = xorBits n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih fun j hj => h j (by omega)]
    split
    · rename_i hv; rw [h n (by omega) hv]
    · rfl

theorem testBit_eq_false_of_lt {v k j : ℕ} (hv : v < 2 ^ k) (hj : k ≤ j) : v.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right Nat.two_pos hj))

theorem outer_lt (a b : ℕ) : outer a b < 512 := by
  unfold outer
  have h7 : b &&& 7 < 8 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h1 : (if a.testBit 0 then b &&& 7 else 0) < 2 ^ 9 := by
    split <;> omega
  have h2 : (if a.testBit 1 then (b &&& 7) <<< 3 else 0) < 2 ^ 9 := by
    split
    · rw [Nat.shiftLeft_eq]; omega
    · omega
  have h3 : (if a.testBit 2 then (b &&& 7) <<< 6 else 0) < 2 ^ 9 := by
    split
    · rw [Nat.shiftLeft_eq]; omega
    · omega
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h1 h2) h3

theorem qOf_lt (u : Bool) (v : ℕ) : qOf u v < 512 := by
  unfold qOf
  refine Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (outer_lt _ _) (outer_lt _ _)) ?_
  split
  · exact outer_lt _ _
  · norm_num

@[expose] def Valid (B : ℕ → ℕ) (rows : List (ℕ × ℕ)) : Prop :=
  ∀ r ∈ rows, r.1 < 512 ∧ B r.1 = r.2

variable {B : ℕ → ℕ}

theorem lmRed_inv (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y) :
    ∀ (rows : List (ℕ × ℕ)) (p : ℕ × ℕ), Valid B rows → p.1 < 512 →
      (lmRed rows p).1 < 512 ∧ (lmRed rows p).2 ^^^ B (lmRed rows p).1 = p.2 ^^^ B p.1 := by
  intro rows
  induction rows with
  | nil => intro p _ hp; exact ⟨hp, rfl⟩
  | cons r rows ih =>
    intro p hv hp
    have hr := hv r List.mem_cons_self
    have hv' : Valid B rows := fun r' hr' => hv r' (List.mem_cons_of_mem _ hr')
    change (lmRed rows (if p.1 ^^^ r.1 < p.1 then (p.1 ^^^ r.1, p.2 ^^^ r.2) else p)).1 < 512 ∧
      (lmRed rows (if p.1 ^^^ r.1 < p.1 then (p.1 ^^^ r.1, p.2 ^^^ r.2) else p)).2 ^^^
        B (lmRed rows (if p.1 ^^^ r.1 < p.1 then (p.1 ^^^ r.1, p.2 ^^^ r.2) else p)).1 =
        p.2 ^^^ B p.1
    split
    · obtain ⟨h1, h2⟩ := ih (p.1 ^^^ r.1, p.2 ^^^ r.2) hv' (Nat.xor_lt_two_pow (n := 9) hp hr.1)
      refine ⟨h1, h2.trans ?_⟩
      change p.2 ^^^ r.2 ^^^ B (p.1 ^^^ r.1) = p.2 ^^^ B p.1
      rw [hB _ _ hp hr.1, hr.2, Nat.xor_assoc, ← Nat.xor_assoc r.2, Nat.xor_comm r.2 (B p.1),
        Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    · exact ih _ hv' hp

theorem lmRed_valid (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (rows : List (ℕ × ℕ)) (p : ℕ × ℕ) (hv : Valid B rows) (hp : p.1 < 512) (hBp : B p.1 = p.2) :
    (lmRed rows p).1 < 512 ∧ B (lmRed rows p).1 = (lmRed rows p).2 := by
  obtain ⟨h1, h2⟩ := lmRed_inv hB rows p hv hp
  refine ⟨h1, ?_⟩
  rw [hBp, Nat.xor_self] at h2
  have := congrArg (· ^^^ B (lmRed rows p).1) h2
  simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this
  exact this.symm

theorem B_zero (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y) : B 0 = 0 := by
  have h := hB 0 0 (by norm_num) (by norm_num)
  rw [Nat.xor_self] at h
  have h2 : B 0 ^^^ B 0 = 0 := Nat.xor_self _
  rw [← h] at h2
  exact h2

theorem lmAdd_valid (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    {rows : List (ℕ × ℕ)} (hv : Valid B rows) {x y : ℕ} (hx : x < 512) (hxy : B x = y) :
    ∃ rows', lmAdd rows x y = some rows' ∧ Valid B rows' := by
  obtain ⟨h1, h2⟩ := lmRed_valid hB rows (x, y) hv hx hxy
  unfold lmAdd
  simp only
  split
  · rename_i h0
    rw [h0, B_zero hB] at h2
    rw [ite_eq_left h2.symm]
    exact ⟨rows, rfl, hv⟩
  · refine ⟨_, rfl, fun r hr => ?_⟩
    rcases (List.mem_orderedInsert _).1 hr with rfl | hr
    · exact ⟨h1, h2⟩
    · exact hv r hr

variable {u : Bool} {A : ℕ → ℕ}

@[expose] def pre (A : ℕ → ℕ) (k : ℕ) : List ℕ := (List.range k).map fun j => A (2 ^ j)

theorem pre_succ (k : ℕ) : pre A (k + 1) = pre A k ++ [A (2 ^ k)] := by
  simp [pre, List.range_succ]

theorem getD_pre {k j : ℕ} (hj : j < k) : (pre A k).getD j 0 = A (2 ^ j) := by
  rw [List.getD_eq_getElem _ _ (by simpa [pre] using hj)]
  simp [pre]

theorem evalV_pre (hA : ∀ v w, v < 64 → w < 64 → A (v ^^^ w) = A v ^^^ A w) {k v : ℕ}
    (hk : k ≤ 6) (hv : v < 2 ^ k) : evalV (pre A k) v = A v := by
  have hv64 : v < 2 ^ 6 := lt_of_lt_of_le hv (Nat.pow_le_pow_right Nat.two_pos hk)
  rw [eq_xorBits (n := 6) hA hv64]
  unfold evalV
  refine xorBits_congr_bits fun j _ hbit => ?_
  have hjk : j < k := by
    by_contra hjk
    rw [testBit_eq_false_of_lt hv (by omega)] at hbit
    exact Bool.false_ne_true hbit
  exact getD_pre hjk

theorem addNew_valid (hA : ∀ v w, v < 64 → w < 64 → A (v ^^^ w) = A v ^^^ A w)
    (hA0 : ∀ v, v < 64 → A v = 0 → v = 0)
    (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (hq : ∀ v, v < 64 → qOf u (A v) = B (qOf u v)) {k : ℕ} (hk : k < 6)
    {rows : List (ℕ × ℕ)} (hv : Valid B rows) :
    ∃ rows', addNew u (pre A (k + 1)) k rows = some rows' ∧ Valid B rows' := by
  unfold addNew
  have key : ∀ (l : List ℕ) (acc : Option (List (ℕ × ℕ))), (∀ u₀ ∈ l, u₀ < 2 ^ k) →
      (∃ rs, acc = some rs ∧ Valid B rs) →
      ∃ rs, l.foldl (fun acc u₀ => acc.bind fun rs =>
        if evalV (pre A (k + 1)) (2 ^ k + u₀) = 0 then none
        else lmAdd rs (qOf u (2 ^ k + u₀)) (qOf u (evalV (pre A (k + 1)) (2 ^ k + u₀)))) acc =
          some rs ∧ Valid B rs := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons u₀ l ih =>
      intro acc hl ⟨rs, hacc, hrs⟩
      rw [List.foldl_cons]
      apply ih _ fun w hw => hl w (List.mem_cons_of_mem _ hw)
      have hu₀ : u₀ < 2 ^ k := hl u₀ List.mem_cons_self
      have hlt : 2 ^ k + u₀ < 2 ^ (k + 1) := by rw [pow_succ]; omega
      have h64 : 2 ^ k + u₀ < 64 :=
        lt_of_lt_of_le hlt (by
          calc 2 ^ (k + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right Nat.two_pos (by omega)
            _ = 64 := by norm_num)
      have hev : evalV (pre A (k + 1)) (2 ^ k + u₀) = A (2 ^ k + u₀) :=
        evalV_pre hA (by omega) hlt
      rw [hacc, Option.bind_some, hev, ite_eq_right fun h0 => by
        have := hA0 _ h64 h0
        have : 0 < 2 ^ k := Nat.two_pow_pos k
        omega]
      exact lmAdd_valid hB hrs (qOf_lt u _) (hq _ h64).symm
  exact key _ _ (fun w hw => List.mem_range.1 hw) ⟨rows, rfl, hv⟩

theorem mem_fibOf {u : Bool} {y v : ℕ} (hy : y < 512) :
    v ∈ (fibOf u).getD y [] ↔ v < 64 ∧ qOf u v = y := by
  have key : ∀ b : Bool, v ∈ (fibTab b).getD y [] ↔ v < 64 ∧ qOf b v = y := fun b => by
    unfold fibTab
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
      List.getElem?_range hy]
    simp [List.mem_filter, List.mem_range]
  unfold fibOf fibU fibL
  cases u <;> exact key _

theorem mem_cands (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (hAlt : ∀ v, v < 64 → A v < 64) (hq : ∀ v, v < 64 → qOf u (A v) = B (qOf u v))
    {k : ℕ} (hk : k < 6) {rows : List (ℕ × ℕ)} (hv : Valid B rows) :
    A (2 ^ k) ∈ cands u k rows := by
  have hk64 : 2 ^ k < 64 :=
    calc 2 ^ k < 2 ^ 6 := Nat.pow_lt_pow_right Nat.one_lt_two hk
      _ = 64 := by norm_num
  unfold cands
  split
  · rename_i h0
    obtain ⟨-, h2⟩ := lmRed_inv hB rows (qOf u (2 ^ k), 0) hv (qOf_lt u _)
    rw [h0, B_zero hB, Nat.xor_zero, Nat.zero_xor] at h2
    simp only at h2
    have hy : (lmRed rows (qOf u (2 ^ k), 0)).2 < 512 := by
      rw [h2, ← hq _ hk64]
      exact qOf_lt u _
    rw [mem_fibOf hy, h2]
    exact ⟨hAlt _ hk64, hq _ hk64⟩
  · exact List.mem_range.2 (hAlt _ hk64)

theorem mem_oqStatesFrom (hA : ∀ v w, v < 64 → w < 64 → A (v ^^^ w) = A v ^^^ A w)
    (hAlt : ∀ v, v < 64 → A v < 64) (hA0 : ∀ v, v < 64 → A v = 0 → v = 0)
    (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (hq : ∀ v, v < 64 → qOf u (A v) = B (qOf u v)) :
    ∀ m, m ≤ 5 → ∃ rows, Valid B rows ∧ (pre A (m + 1), rows) ∈ oqStatesFrom u (A 1) m := by
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨rows, hadd, hv⟩ := addNew_valid hA hA0 hB hq (k := 0) (by omega)
      (fun r hr => absurd hr List.not_mem_nil)
    refine ⟨rows, hv, ?_⟩
    have hpre : pre A 1 = [A 1] := rfl
    rw [hpre] at hadd ⊢
    simp [oqStatesFrom, hadd]
  | succ m ih =>
    intro hm
    obtain ⟨rows, hv, hmem⟩ := ih (by omega)
    obtain ⟨rows', hadd, hv'⟩ := addNew_valid hA hA0 hB hq (k := m + 1) (by omega) hv
    refine ⟨rows', hv', ?_⟩
    rw [oqStatesFrom, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine List.mem_flatMap.2 ⟨_, hmem, ?_⟩
    unfold oqStep
    refine List.mem_filterMap.2 ⟨A (2 ^ (m + 1)), mem_cands hB hAlt hq (by omega) hv, ?_⟩
    rw [← pre_succ, hadd]
    rfl

theorem mem_oqFrom (hA : ∀ v w, v < 64 → w < 64 → A (v ^^^ w) = A v ^^^ A w)
    (hAlt : ∀ v, v < 64 → A v < 64) (hA0 : ∀ v, v < 64 → A v = 0 → v = 0)
    (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (hq : ∀ v, v < 64 → qOf u (A v) = B (qOf u v)) :
    (List.range 6).map (fun j => A (2 ^ j)) ∈ oqFrom u (A 1) := by
  obtain ⟨rows, -, hmem⟩ := mem_oqStatesFrom hA hAlt hA0 hB hq 5 le_rfl
  exact List.mem_map.2 ⟨_, hmem, rfl⟩

theorem mem_oqSearch (hA : ∀ v w, v < 64 → w < 64 → A (v ^^^ w) = A v ^^^ A w)
    (hAlt : ∀ v, v < 64 → A v < 64) (hA0 : ∀ v, v < 64 → A v = 0 → v = 0)
    (hB : ∀ x y, x < 512 → y < 512 → B (x ^^^ y) = B x ^^^ B y)
    (hq : ∀ v, v < 64 → qOf u (A v) = B (qOf u v)) :
    (List.range 6).map (fun j => A (2 ^ j)) ∈ oqSearch u :=
  List.mem_flatMap.2 ⟨A 1, List.mem_range.2 (hAlt 1 (by norm_num)),
    mem_oqFrom hA hAlt hA0 hB hq⟩

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne
