module

public import CFSG.Certificates.Kernel.Th.Spec.SurjText
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.Sporadic.Bridge.Th

@[expose] def lettOfCode (x : ℕ) : ℕ × Bool := (x / 2, decide (x % 2 = 0))

private theorem swAndB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem swBeq {a b : ℕ} : Nat.beq a b = true ↔ a = b := iff_of_eq Nat.beq_eq

private theorem swBlt {a b : ℕ} : Nat.blt a b = true ↔ a < b := iff_of_eq Nat.blt_eq

private theorem swCodesEq (l : List Char) :
    ∀ m : List ℕ, codesEq l m = true ↔ l.map Char.toNat = m := by
  induction l with
  | nil =>
    intro m
    cases m with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y t =>
      exact ⟨fun h => absurd (show false = true from h) Bool.false_ne_true,
        fun h => absurd h (by simp)⟩
  | cons ch l ih =>
    intro m
    cases m with
    | nil =>
      exact ⟨fun h => absurd (show false = true from h) Bool.false_ne_true,
        fun h => absurd h (by simp)⟩
    | cons y t =>
      show andB (Nat.beq ch.toNat y) (codesEq l t) = true ↔ _
      rw [swAndB, swBeq, ih t, List.map_cons, List.cons.injEq]

private theorem swNonempty (w : List ℕ) :
    (List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) w) = true ↔ w ≠ [] := by
  cases w <;> simp

private theorem swAll8 (w : List ℕ) :
    (List.rec (motive := fun _ => Bool) true
      (fun x _ ih2 => andB ih2 (Nat.blt (Nat.shiftRight x 1) 8)) w) = true ↔
      ∀ x ∈ w, x / 2 < 8 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have e : Nat.shiftRight x 1 = x / 2 := Nat.shiftRight_one x
    show andB _ (Nat.blt (Nat.shiftRight x 1) 8) = true ↔ _
    rw [swAndB, ih, swBlt, List.forall_mem_cons, e, and_comm]

private theorem swLettersOK : ∀ ws : List (List ℕ), lettersOK ws = true ↔
    ∀ w ∈ ws, w ≠ [] ∧ ∀ x ∈ w, x / 2 < 8
  | [] => by simp [lettersOK]
  | w :: ws => by
    have ih := swLettersOK ws
    show andB (lettersOK ws) (andB (List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) w)
      (List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => andB ih2 (Nat.blt (Nat.shiftRight x 1) 8)) w)) = true ↔ _
    rw [swAndB, swAndB, ih, swNonempty, swAll8, List.forall_mem_cons]
    tauto

private theorem swWordsChars (ws : List (List ℕ)) :
    wordsChars ws = (ws.map wordChars).flatten := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    show List.append (wordChars w) (wordsChars ws) = _
    rw [ih]
    simp

@[expose] def joinSp : List (List ℕ) → List ℕ
  | [] => []
  | [t] => t
  | t :: u :: r => t ++ 32 :: joinSp (u :: r)

@[expose] def joinSpC : List (List Char) → List Char
  | [] => []
  | [t] => t
  | t :: u :: r => t ++ ' ' :: joinSpC (u :: r)

private theorem swWordChars : ∀ w : List ℕ, wordChars w = joinSp (w.map letterChars) ++ [10]
  | [] => rfl
  | [x] => by
    have e : wordChars [x] = letterChars x ++ [10] := rfl
    rw [e]
    simp [joinSp]
  | x :: y :: t => by
    have ih := swWordChars (y :: t)
    have e : wordChars (x :: y :: t) = letterChars x ++ 32 :: wordChars (y :: t) := rfl
    rw [e, ih]
    simp [joinSp]

@[expose] noncomputable def letterStr (x : ℕ) : List Char := (letterChars x).map Char.ofNat

@[expose] def codeInt (x : ℕ) : ℤ :=
  if x % 2 = 1 then -((x / 2 + 1 : ℕ) : ℤ) else ((x / 2 + 1 : ℕ) : ℤ)

private theorem swLetterChars (x : ℕ) :
    letterChars x = if x % 2 = 1 then [45, 49 + x / 2] else [49 + x / 2] := by
  have e1 : Nat.shiftRight x 1 = x / 2 := Nat.shiftRight_one x
  have e2 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
  unfold letterChars
  rw [e1, e2]
  by_cases h : x % 2 = 1
  · have : Nat.beq (x % 2) 1 = true := swBeq.2 h
    simp [this, h]
  · have : Nat.beq (x % 2) 1 = false := by
      cases hh : Nat.beq (x % 2) 1
      · rfl
      · exact absurd (swBeq.1 hh) h
    simp [this, h]

private theorem swDigit {g : ℕ} (hg : g < 8) :
    (Char.ofNat (49 + g)).isDigit = true ∧ (Char.ofNat (49 + g)).toNat = 49 + g := by
  interval_cases g <;> decide

private theorem swLetterStr {x : ℕ} (hx : x / 2 < 8) :
    letterStr x =
      if x % 2 = 1 then ['-', Char.ofNat (49 + x / 2)] else [Char.ofNat (49 + x / 2)] := by
  unfold letterStr
  rw [swLetterChars]
  split_ifs <;> simp [show Char.ofNat 45 = '-' from rfl]

private theorem swTokInt {x : ℕ} (hx : x / 2 < 8) :
    (String.ofList (letterStr x)).toInt? = some (codeInt x) := by
  obtain ⟨hdig, htoNat⟩ := swDigit hx
  have hnat : (String.ofList [Char.ofNat (49 + x / 2)]).toNat? = some (x / 2 + 1) := by
    have hn : (String.ofList [Char.ofNat (49 + x / 2)]).isNat = true :=
      String.isNat_of_isDigit (by simp) (by simpa using hdig)
    have hd1 : (Char.ofNat (49 + x / 2) != '_') = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h
      have h2 := congrArg Char.toNat h
      rw [htoNat] at h2
      have h3 : ('_' : Char).toNat = 95 := rfl
      omega
    have hf : List.filter (fun c => c != '_') [Char.ofNat (49 + x / 2)] =
        [Char.ofNat (49 + x / 2)] :=
      List.filter_eq_self.2 fun c hc => by
        rw [List.mem_singleton] at hc
        subst hc
        exact hd1
    rw [String.toNat?_eq_some_ofDigitChars hn, String.toList_ofList, hf]
    simp [Nat.ofDigitChars_eq_foldl, htoNat]
    omega
  unfold codeInt
  rw [swLetterStr hx]
  by_cases h : x % 2 = 1
  · simp only [h, if_true]
    have e : String.ofList ['-', Char.ofNat (49 + x / 2)] =
        "-" ++ String.ofList [Char.ofNat (49 + x / 2)] := by
      apply String.toList_injective
      simp
    rw [e, String.toInt?_minus_append, hnat]
    rfl
  · simp only [h, if_false]
    exact String.toInt?_eq_some_of_toNat?_eq_some hnat

private theorem swTokChars {x : ℕ} (hx : x / 2 < 8) : ∀ c ∈ letterStr x, c ≠ ' ' ∧ c ≠ '\n' := by
  obtain ⟨-, htoNat⟩ := swDigit hx
  rw [swLetterStr hx]
  intro c hc
  split_ifs at hc
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨by decide, by decide⟩
    · rw [List.mem_singleton] at hc
      subst hc
      constructor <;> intro h <;> rw [h] at htoNat <;> simp at htoNat <;> omega
  · rw [List.mem_singleton] at hc
    subst hc
    constructor <;> intro h <;> rw [h] at htoNat <;> simp at htoNat <;> omega

private theorem swTokNe (x : ℕ) (hx : x / 2 < 8) : letterStr x ≠ [] := by
  rw [swLetterStr hx]
  split_ifs <;> simp

private theorem swJoinMem : ∀ (ts : List (List Char)) (c : Char), c ∈ joinSpC ts →
    c = ' ' ∨ ∃ t ∈ ts, c ∈ t
  | [], c, h => by simp [joinSpC] at h
  | [t], c, h => Or.inr ⟨t, by simp, h⟩
  | t :: u :: r, c, h => by
    have h' : c ∈ t ++ ' ' :: joinSpC (u :: r) := h
    rcases List.mem_append.1 h' with h1 | h1
    · exact Or.inr ⟨t, by simp, h1⟩
    · rcases List.mem_cons.1 h1 with h2 | h2
      · exact Or.inl h2
      · rcases swJoinMem (u :: r) c h2 with h3 | ⟨s, hs, h4⟩
        · exact Or.inl h3
        · exact Or.inr ⟨s, by simp [hs], h4⟩

private theorem swJoinNe :
    ∀ (t : List Char) (ts : List (List Char)), t ≠ [] → joinSpC (t :: ts) ≠ []
  | t, [], ht => by simpa [joinSpC] using ht
  | t, u :: r, _ => by simp [joinSpC]

private theorem swJoinSp_map : ∀ ts : List (List ℕ),
    (joinSp ts).map Char.ofNat = joinSpC (ts.map (List.map Char.ofNat))
  | [] => rfl
  | [t] => rfl
  | t :: u :: r => by
    have ih := swJoinSp_map (u :: r)
    simp only [joinSp, joinSpC, List.map_cons, List.map_append, ih]

private theorem swSplitJoin : ∀ ts : List (List Char), ts ≠ [] → (∀ t ∈ ts, ∀ c ∈ t, c ≠ ' ') →
    (joinSpC ts).splitOnP (· == ' ') = ts
  | [], h, _ => absurd rfl h
  | [t], _, hf => by
    show t.splitOnP (· == ' ') = [t]
    exact List.splitOnP_eq_singleton (fun c hc => by simpa using hf t (by simp) c hc)
  | t :: u :: r, _, hf => by
    show (t ++ ' ' :: joinSpC (u :: r)).splitOnP (· == ' ') = _
    rw [List.splitOnP_append_cons_of_forall_mem
      (fun c hc => by simpa using hf t (by simp) c hc) ' ' (by simp),
      swSplitJoin (u :: r) (by simp) (fun s hs => hf s (by simp [hs]))]

private theorem swLetterOfInt {x : ℕ} : letterOfInt (codeInt x) = lettOfCode x := by
  rcases Nat.mod_two_eq_zero_or_one x with h | h
  · have hc : codeInt x = ((x / 2 + 1 : ℕ) : ℤ) := by
      unfold codeInt
      simp [h]
    have hp : (0 : ℤ) < ((x / 2 + 1 : ℕ) : ℤ) := by omega
    rw [hc]
    unfold letterOfInt lettOfCode
    rw [if_pos hp]
    refine Prod.ext ?_ ?_
    · show (((x / 2 + 1 : ℕ) : ℤ) - 1).toNat = x / 2
      omega
    · show true = decide (x % 2 = 0)
      simp [h]
  · have hc : codeInt x = -((x / 2 + 1 : ℕ) : ℤ) := by
      unfold codeInt
      simp [h]
    have hp : ¬ (0 : ℤ) < -((x / 2 + 1 : ℕ) : ℤ) := by omega
    rw [hc]
    unfold letterOfInt lettOfCode
    rw [if_neg hp]
    refine Prod.ext ?_ ?_
    · show (-(-((x / 2 + 1 : ℕ) : ℤ)) - 1).toNat = x / 2
      omega
    · show false = decide (x % 2 = 0)
      simp [h]

private theorem swFilterInts : ∀ w : List ℕ, (∀ x ∈ w, x / 2 < 8) →
    ((w.map letterStr).map String.ofList).filterMap String.toInt? = w.map codeInt
  | [], _ => rfl
  | x :: w, hx => by
    simp only [List.map_cons, List.filterMap_cons, swTokInt (hx x (by simp))]
    rw [swFilterInts w (fun y hy => hx y (by simp [hy]))]

private theorem swParseWord {w : List ℕ} (hw : w ≠ []) (hx : ∀ x ∈ w, x / 2 < 8) :
    parseWord (String.ofList (joinSpC (w.map letterStr))) = w.map lettOfCode := by
  have hs : " " = String.singleton ' ' := by decide
  have hchars : ∀ t ∈ w.map letterStr, ∀ c ∈ t, c ≠ ' ' := by
    intro t ht c hc
    obtain ⟨x, hxw, rfl⟩ := List.mem_map.1 ht
    exact (swTokChars (hx x hxw) c hc).1
  unfold parseWord
  rw [hs, CFSG.KC.Str.splitOn_ofList, List.splitOn_eq_splitOnP,
    swSplitJoin _ (by simpa using hw) hchars, swFilterInts w hx, List.map_map]
  exact List.map_congr_left (fun x _ => swLetterOfInt)

private theorem swLines (ws : List (List ℕ)) :
    (wordsChars ws).map Char.ofNat =
      ((ws.map fun w => joinSpC (w.map letterStr)).map fun p => p ++ ['\n']).flatten := by
  rw [swWordsChars, List.map_flatten, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp_apply, swWordChars, List.map_append, swJoinSp_map, List.map_map]
  rfl

theorem parseWords_spec {ws : List (List ℕ)} {l : List Char} (h : wordsOK l ws = true) :
    (∀ w ∈ ws, w ≠ [] ∧ ∀ x ∈ w, x / 2 < 8) ∧
      parseWords (String.ofList l) = ws.map (List.map lettOfCode) := by
  obtain ⟨h1, h2⟩ := swAndB.1 h
  have hws := (swLettersOK ws).1 h1
  refine ⟨hws, ?_⟩
  have hl : l = (wordsChars ws).map Char.ofNat := by
    rw [← (swCodesEq l _).1 h2, List.map_map]
    have e : (Char.ofNat ∘ Char.toNat) = id := funext fun c => Char.ofNat_toNat c
    rw [e, List.map_id]
  have hne : ∀ p ∈ ws.map (fun w => joinSpC (w.map letterStr)), p ≠ [] := by
    intro p hp
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
    obtain ⟨hw0, hwx⟩ := hws w hw
    obtain ⟨x, w', rfl⟩ := List.exists_cons_of_ne_nil hw0
    exact swJoinNe _ _ (swTokNe x (hwx x (by simp)))
  have hnl : ∀ p ∈ ws.map (fun w => joinSpC (w.map letterStr)), ∀ ch ∈ p, ch ≠ '\n' := by
    intro p hp ch hch
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
    obtain ⟨-, hwx⟩ := hws w hw
    rcases swJoinMem _ ch hch with rfl | ⟨t, ht, hct⟩
    · decide
    · obtain ⟨x, hxw, rfl⟩ := List.mem_map.1 ht
      exact (swTokChars (hwx x hxw) ch hct).2
  rw [hl, swLines]
  unfold parseWords
  rw [splitLines_ofList hne hnl, List.map_map, List.map_map]
  refine List.map_congr_left fun w hw => ?_
  obtain ⟨hw0, hwx⟩ := hws w hw
  exact swParseWord hw0 hwx

end CFSG.KC.Th.Spec

end
