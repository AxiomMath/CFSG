module

public import Certificates.Data.E8TenTwo
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
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

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open E8TenTwo

theorem getD_of_le {α : Type _} (l : List α) (d : α) {i : Nat} (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getD_of_lt {α : Type _} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem xor_xor_xor_cancel (a b c : Nat) : (a ^^^ c) ^^^ (b ^^^ c) = a ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem xor_swap_right (a b c : Nat) : (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

theorem lin_induct {P : Nat → Prop} (h0 : P 0) (hbasis : ∀ j < 20, P (1 <<< j))
    (hxor : ∀ x y, P x → P y → P (x ^^^ y)) : ∀ b, b < 2 ^ 20 → P b := by
  have key : ∀ n, n ≤ 20 → ∀ b, b < 2 ^ n → P b := by
    intro n
    induction n with
    | zero =>
      intro _ b hb
      have : b = 0 := by simpa using hb
      subst this
      exact h0
    | succ n ih =>
      intro hn b hb
      by_cases hbit : b.testBit n = true
      · have hb' : b ^^^ 2 ^ n < 2 ^ n := by
          apply Nat.lt_pow_two_of_testBit
          intro i hi
          rw [Nat.testBit_xor, Nat.testBit_two_pow]
          rcases Nat.eq_or_lt_of_le hi with h | h
          · subst h
            simp [hbit]
          · have h1 : b.testBit i = false :=
              Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h)))
            have h2 : ¬ (n = i) := by omega
            simp [h1, h2]
        have e : b = (b ^^^ 2 ^ n) ^^^ 2 ^ n := by
          rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [e]
        refine hxor _ _ (ih (by omega) _ hb') ?_
        have := hbasis n (by omega)
        rwa [Nat.one_shiftLeft] at this
      · have hfalse : b.testBit n = false := by simpa using hbit
        have hb' : b < 2 ^ n := by
          apply Nat.lt_pow_two_of_testBit
          intro i hi
          rcases Nat.eq_or_lt_of_le hi with h | h
          · rw [← h]
            exact hfalse
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h)))
        exact ih (by omega) b hb'
  intro b hb
  exact key 20 le_rfl b hb

theorem foldl_testBit_xor (cols : List Nat) (v v' : Nat) (l : List Nat) (a a' : Nat) :
    l.foldl (fun acc j => if (v ^^^ v').testBit j then acc ^^^ cols.getD j 0 else acc) (a ^^^ a') =
      l.foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) a ^^^
        l.foldl (fun acc j => if v'.testBit j then acc ^^^ cols.getD j 0 else acc) a' := by
  induction l generalizing a a' with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    by_cases h1 : v.testBit j = true <;> by_cases h2 : v'.testBit j = true
    · have h3 : ¬ (v ^^^ v').testBit j = true := by
        rw [Nat.testBit_xor, h1, h2]
        decide
      rw [if_neg h3, if_pos h1, if_pos h2, ← xor_xor_xor_cancel a a' (cols.getD j 0)]
      exact ih (a ^^^ cols.getD j 0) (a' ^^^ cols.getD j 0)
    · have h2' : v'.testBit j = false := by simpa using h2
      have h3 : (v ^^^ v').testBit j = true := by
        rw [Nat.testBit_xor, h1, h2']
        decide
      rw [if_pos h3, if_pos h1, if_neg h2, xor_swap_right a a' (cols.getD j 0)]
      exact ih (a ^^^ cols.getD j 0) a'
    · have h1' : v.testBit j = false := by simpa using h1
      have h3 : (v ^^^ v').testBit j = true := by
        rw [Nat.testBit_xor, h1', h2]
        decide
      rw [if_pos h3, if_neg h1, if_pos h2, Nat.xor_assoc]
      exact ih a (a' ^^^ cols.getD j 0)
    · have h1' : v.testBit j = false := by simpa using h1
      have h2' : v'.testBit j = false := by simpa using h2
      have h3 : ¬ (v ^^^ v').testBit j = true := by
        rw [Nat.testBit_xor, h1', h2']
        decide
      rw [if_neg h3, if_neg h1, if_neg h2]
      exact ih a a'

theorem applyCols_xor (cols : List Nat) (v v' : Nat) :
    applyCols cols (v ^^^ v') = applyCols cols v ^^^ applyCols cols v' := by
  unfold applyCols
  have h := foldl_testBit_xor cols v v' (List.range 20) 0 0
  rwa [Nat.xor_zero] at h

theorem applyCols_zero (cols : List Nat) : applyCols cols 0 = 0 := by
  have h := applyCols_xor cols 0 0
  rw [Nat.xor_zero, Nat.xor_self] at h
  exact h

theorem foldl_single_bit (c : Nat → Nat) (j : Nat) (n a : Nat) :
    (List.range n).foldl (fun acc i => if (1 <<< j).testBit i then acc ^^^ c i else acc) a =
      if j < n then a ^^^ c j else a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : j = n
    · subst h
      simp
    · have h1 : j < n + 1 ↔ j < n := by omega
      simp [h, h1]

theorem applyCols_pow (cols : List Nat) {j : Nat} (hj : j < 20) :
    applyCols cols (1 <<< j) = cols.getD j 0 := by
  unfold applyCols
  have h := foldl_single_bit (fun i => cols.getD i 0) j 20 0
  simp only [if_pos hj, Nat.zero_xor] at h
  exact h

theorem applyWord_cons (M : List (List Nat)) (g : Nat) (w : List Nat) (v : Nat) :
    applyWord M (g :: w) v = applyCols (M.getD g []) (applyWord M w v) := rfl

theorem applyWord_nil (M : List (List Nat)) (v : Nat) : applyWord M [] v = v := rfl

theorem applyWord_xor (M : List (List Nat)) (w : List Nat) (v v' : Nat) :
    applyWord M w (v ^^^ v') = applyWord M w v ^^^ applyWord M w v' := by
  induction w with
  | nil => rfl
  | cons g w ih => rw [applyWord_cons, applyWord_cons, applyWord_cons, ih, applyCols_xor]

theorem applyWord_zero (M : List (List Nat)) (w : List Nat) : applyWord M w 0 = 0 := by
  have h := applyWord_xor M w 0 0
  rw [Nat.xor_zero, Nat.xor_self] at h
  exact h

theorem applyCols_compCols (M : List (List Nat)) (w : List Nat) :
    ∀ v, v < 2 ^ 20 → applyCols (compCols M w) v = applyWord M w v := by
  apply lin_induct (P := fun v => applyCols (compCols M w) v = applyWord M w v)
  · rw [applyCols_zero, applyWord_zero]
  · intro j hj
    rw [applyCols_pow _ hj]
    unfold compCols
    simp [List.getD_eq_getElem?_getD, hj]
  · intro x y hx hy
    rw [applyCols_xor, applyWord_xor, hx, hy]

theorem foldl_cols_lt (cols : List Nat) (hc : ∀ j, cols.getD j 0 < 2 ^ 20) (v : Nat) (l : List Nat)
    (a : Nat) (ha : a < 2 ^ 20) :
    l.foldl (fun acc j => if v.testBit j then acc ^^^ cols.getD j 0 else acc) a < 2 ^ 20 := by
  induction l generalizing a with
  | nil => exact ha
  | cons j l ih =>
    simp only [List.foldl_cons]
    apply ih
    split_ifs
    · exact Nat.xor_lt_two_pow ha (hc j)
    · exact ha

theorem applyCols_lt (cols : List Nat) (hc : ∀ j, cols.getD j 0 < 2 ^ 20) (v : Nat) :
    applyCols cols v < 2 ^ 20 :=
  foldl_cols_lt cols hc v _ 0 (by positivity)

theorem f4sq_lt : ∀ x, x < 4 → f4sq x < 4 := by decide

theorem f4mulW_lt : ∀ x, x < 4 → f4mulW x < 4 := by decide

theorem f4mul_lt (s : Nat) : ∀ x, x < 4 → f4mul s x < 4 := by
  intro x hx
  unfold f4mul
  split_ifs
  · exact hx
  · exact f4mulW_lt x hx

theorem f4sq_xor : ∀ x, x < 4 → ∀ y, y < 4 → f4sq (x ^^^ y) = f4sq x ^^^ f4sq y := by decide

theorem xor_lt_four {x y : Nat} (hx : x < 4) (hy : y < 4) : x ^^^ y < 4 := by
  have := Nat.xor_lt_two_pow (n := 2) (x := x) (y := y) hx hy
  simpa using this

theorem expandV_length (v : Nat) : (expandV v).length = 20 := by
  simp [expandV]

theorem expandV_getD {v i : Nat} (hi : i < 20) :
    (expandV v).getD i 0 =
      if i % 2 = 0 then (v >>> (2 * (i / 2))) &&& 3 else f4sq ((v >>> (2 * (i / 2))) &&& 3) := by
  unfold expandV
  simp [List.getD_eq_getElem?_getD, hi]

theorem expandV_getD_out {v i : Nat} (hi : 20 ≤ i) : (expandV v).getD i 0 = 0 := by
  exact getD_of_le _ _ (by rw [expandV_length]; exact hi)

theorem and_three_lt (x : Nat) : x &&& 3 < 4 := by
  have := Nat.and_lt_two_pow x (y := 3) (n := 2) (by norm_num)
  simpa using this

theorem expandV_lt (v i : Nat) : (expandV v).getD i 0 < 4 := by
  by_cases hi : i < 20
  · rw [expandV_getD hi]
    split_ifs
    · exact and_three_lt _
    · exact f4sq_lt _ (and_three_lt _)
  · rw [expandV_getD_out (by omega)]
    norm_num

theorem expandV_xor (v v' i : Nat) :
    (expandV (v ^^^ v')).getD i 0 = (expandV v).getD i 0 ^^^ (expandV v').getD i 0 := by
  by_cases hi : i < 20
  · rw [expandV_getD hi, expandV_getD hi, expandV_getD hi]
    split_ifs
    · rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]
    · rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right,
        f4sq_xor _ (and_three_lt _) _ (and_three_lt _)]
  · rw [expandV_getD_out (by omega), expandV_getD_out (by omega), expandV_getD_out (by omega)]
    rfl

theorem expandV_zero (i : Nat) : (expandV 0).getD i 0 = 0 := by
  by_cases hi : i < 20
  · rw [expandV_getD hi]
    split_ifs <;> simp [f4sq]
  · exact expandV_getD_out (by omega)

theorem expandV_pair : ∀ k < 10, ∀ a < 4, ∀ i < 20, (expandV (a <<< (2 * k))).getD i 0 =
    if i = 2 * k then a else if i = 2 * k + 1 then f4sq a else 0 := by
  decide +kernel

theorem digit_eq (v k : Nat) : (v >>> (2 * k)) &&& 3 = v / 4 ^ k % 4 := by
  have h3 : (3 : Nat) = 2 ^ 2 - 1 := by norm_num
  rw [h3, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem exists_pack (a : Nat → Nat) (ha : ∀ k, a k < 4) :
    ∃ b, b < 2 ^ 20 ∧ ∀ k < 10, (b >>> (2 * k)) &&& 3 = a k := by
  have key : ∀ n, ∃ b, b < 4 ^ n ∧ ∀ k < n, b / 4 ^ k % 4 = a k := by
    intro n
    induction n with
    | zero => exact ⟨0, by norm_num, fun k hk => by omega⟩
    | succ n ih =>
      obtain ⟨b, hb, hd⟩ := ih
      refine ⟨b + a n * 4 ^ n, ?_, ?_⟩
      · have h1 : a n * 4 ^ n ≤ 3 * 4 ^ n := Nat.mul_le_mul_right _ (by have := ha n; omega)
        rw [pow_succ]
        omega
      · intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
        · obtain ⟨m, hm⟩ : ∃ m, n = k + (m + 1) := ⟨n - k - 1, by omega⟩
          have hp : 4 ^ n = 4 ^ k * (4 ^ m * 4) := by
            rw [hm, pow_add, pow_succ]
          have hpos : 0 < 4 ^ k := by positivity
          have e1 : (b + a n * 4 ^ n) / 4 ^ k = b / 4 ^ k + a n * 4 ^ m * 4 := by
            have : b + a n * 4 ^ n = b + (a n * 4 ^ m * 4) * 4 ^ k := by
              rw [hp]; ring
            rw [this, Nat.add_mul_div_right _ _ hpos]
          rw [e1, Nat.add_mul_mod_self_right]
          exact hd k hk
        · subst hk
          have : (b + a k * 4 ^ k) / 4 ^ k = a k := by
            have hpos : 0 < 4 ^ k := by positivity
            rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hb, zero_add]
          rw [this]
          exact Nat.mod_eq_of_lt (ha k)
  obtain ⟨b, hb, hd⟩ := key 10
  refine ⟨b, ?_, fun k hk => ?_⟩
  · have : (4 : Nat) ^ 10 = 2 ^ 20 := by norm_num
    rwa [this] at hb
  · rw [digit_eq]
    exact hd k hk

theorem allBelow_spec (f : Nat → Bool) (n : Nat) (h : allBelow f n = true) :
    ∀ m, 1 ≤ m → m ≤ n → f m = true := by
  induction n with
  | zero => intro m h1 h2; omega
  | succ k ih =>
    intro m h1 h2
    unfold allBelow at h
    by_cases hf : f (k + 1) = true
    · rw [if_pos hf] at h
      rcases Nat.lt_or_ge m (k + 1) with hm | hm
      · exact ih h m h1 (by omega)
      · have : m = k + 1 := by omega
        subst this
        exact hf
    · rw [if_neg hf] at h
      exact absurd h (by simp)

theorem foldl_set_mem (l : List (Nat × Nat × Nat)) (A : Array Bool) (d : Nat)
    (h : (l.foldl (fun a e => a.set! e.1 true) A).getD d false = true) :
    A.getD d false = true ∨ ∃ e ∈ l, e.1 = d := by
  induction l generalizing A with
  | nil => exact Or.inl h
  | cons e l ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨e', he', hd⟩
    · rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h1
      by_cases hed : e.1 = d
      · exact Or.inr ⟨e, List.mem_cons_self, hed⟩
      · rw [if_neg hed] at h1
        exact Or.inl (by rwa [Array.getD_eq_getD_getElem?])
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hd⟩

theorem oSet_spec {d : Nat} (h : (oSet ()).getD d false = true) : ∃ e ∈ bfsTab, e.1 = d := by
  unfold oSet at h
  rcases foldl_set_mem bfsTab _ d h with h1 | h1
  · exfalso
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at h1
    split_ifs at h1 <;> simp at h1
  · exact h1

theorem ratOk_spec (h : ratOk () = true) :
    ∀ g < 8, ∀ j < 20, expandV (gcol g j) = modelGen g (expandV (1 <<< j)) := by
  unfold ratOk at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem colsOk_spec (h : colsOk () = true) : ∀ g j, ((gmats ()).getD g []).getD j 0 < 2 ^ 20 := by
  unfold colsOk at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  intro g j
  by_cases hg : g < (gmats ()).length
  · rw [getD_of_lt _ _ hg]
    have hmem : (gmats ())[g] ∈ gmats () := List.getElem_mem hg
    have := h _ hmem
    by_cases hj : j < ((gmats ())[g]).length
    · rw [getD_of_lt _ _ hj]
      exact this _ (List.getElem_mem hj)
    · rw [getD_of_le _ _ (by omega)]
      norm_num
  · rw [getD_of_le (gmats ()) [] (by omega : (gmats ()).length ≤ g)]
    simp

theorem modelFactor_getD (γ : List Int) (s : Nat) (X : List Nat) {i : Nat} (hi : i < 20) :
    (modelFactor γ s X).getD i 0 = X.getD i 0 ^^^
      (if (srcT γ).getD i 20 < 20 then f4mul s (X.getD ((srcT γ).getD i 20) 0) else 0) := by
  unfold modelFactor
  simp [List.getD_eq_getElem?_getD, hi]

theorem modelFactor_getD_out (γ : List Int) (s : Nat) (X : List Nat) {i : Nat} (hi : 20 ≤ i) :
    (modelFactor γ s X).getD i 0 = 0 := by
  apply getD_of_le
  simp [modelFactor, hi]

theorem modelFactor_lt (γ : List Int) (s : Nat) (X : List Nat) (hX : ∀ i, X.getD i 0 < 4) (i : Nat) :
    (modelFactor γ s X).getD i 0 < 4 := by
  by_cases hi : i < 20
  · rw [modelFactor_getD γ s X hi]
    split_ifs
    · exact xor_lt_four (hX i) (f4mul_lt s _ (hX _))
    · rw [Nat.xor_zero]
      exact hX i
  · rw [modelFactor_getD_out γ s X (by omega)]
    norm_num

theorem modelGen_lt4 (g : Nat) (X : List Nat) (hX : ∀ i, X.getD i 0 < 4) (i : Nat) :
    (modelGen g X).getD i 0 < 4 := by
  unfold modelGen
  generalize genFac g = l
  induction l generalizing i with
  | nil => exact hX i
  | cons p l ih =>
    simp only [List.foldr_cons]
    exact modelFactor_lt _ _ _ (fun i => ih i) i

theorem gmats_getD {g : Nat} (hg : g < 8) : (gmats ()).getD g [] = gcols g := by
  unfold gmats
  rw [getD_of_lt _ _ (by simpa using hg)]
  simp

theorem gcols_getD {g j : Nat} (hj : j < 20) : (gcols g).getD j 0 = gcol g j := by
  unfold gcols
  rw [getD_of_lt _ _ (by simpa using hj)]
  simp

theorem wordsOk_spec (h : wordsOk () = true) : ∀ w ∈ transWords, ∀ g ∈ w, g < 8 := by
  unfold wordsOk at h
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem bfsOk_spec (h : bfsOk () = true) :
    ∀ e < bfsTab.length,
      (∃ k < 10, ((bfsTab.getD e (0, 0, 0)).1 >>> (2 * k)) &&& 3 ≠ 0) ∧
      ((bfsTab.getD e (0, 0, 0)).2.1 = 1000 → (bfsTab.getD e (0, 0, 0)).1 ∈ stdVecs ()) ∧
      ((bfsTab.getD e (0, 0, 0)).2.1 ≠ 1000 →
        (bfsTab.getD e (0, 0, 0)).2.1 < e ∧ (bfsTab.getD e (0, 0, 0)).2.2 < 8 ∧
        (bfsTab.getD e (0, 0, 0)).1 = applyCols ((gmats ()).getD (bfsTab.getD e (0, 0, 0)).2.2 [])
          (bfsTab.getD (bfsTab.getD e (0, 0, 0)).2.1 (0, 0, 0)).1) := by
  unfold bfsOk at h
  simp only [List.all_eq_true, List.mem_range] at h
  intro e he
  have h2 := h e he
  rw [Bool.and_eq_true] at h2
  obtain ⟨hA, hB⟩ := h2
  rw [List.any_eq_true] at hA
  obtain ⟨k, hk, hne⟩ := hA
  refine ⟨⟨k, List.mem_range.1 hk, by simpa using hne⟩, fun hr => ?_, fun hr => ?_⟩
  · rw [if_pos (beq_iff_eq.2 hr)] at hB
    simpa using hB
  · rw [if_neg (by simpa using hr)] at hB
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hB
    obtain ⟨⟨h1, h2'⟩, h3⟩ := hB
    exact ⟨h1, h2', h3⟩

theorem stdVecs_lt : ∀ s ∈ stdVecs (), s < 2 ^ 20 := by decide +kernel

theorem stdVecs_form : ∀ s ∈ stdVecs (), ∃ k ∈ stdRep, ∃ a ∈ ([1, 2, 3] : List Nat), s = a <<< (2 * k) := by
  decide +kernel

theorem stdRep_lt : ∀ k ∈ stdRep, k < 10 := by decide +kernel

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
