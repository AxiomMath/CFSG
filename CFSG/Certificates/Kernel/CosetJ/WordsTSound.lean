module

public import Certificates.Data.Kernel.CosetJ.WordsT
public import Certificates.Data.CFSGNative.Bridge.SuzGPL
public import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

public section

namespace CFSG.KC.WordsT

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.SurjK CFSG.KS.SporSch.LyTxt

@[expose] def lineW (l : List Char) : List Int := (List.splitOnP (· == ' ') l).filterMap tv

@[expose] def textW (ls : List (List Char)) : List (List Int) :=
  (ls.filter fun l => !l.isEmpty).map lineW

@[expose] def PreOK (p : List Char) (st sg v : Nat) : Prop :=
  (st = 0 ∧ p = []) ∨ (st = 1 ∧ sg = 1 ∧ v = 0 ∧ p = ['-']) ∨
    (st = 2 ∧ ∃ ds : List Char, ds ≠ [] ∧ (∀ c ∈ ds, c.isDigit = true) ∧
      v = Nat.ofDigitChars 10 ds 0 ∧ ((sg = 0 ∧ p = ds) ∨ (sg = 1 ∧ p = '-' :: ds)))

theorem strictB_eqM (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem digit_ne {c : Char} (h : c.isDigit = true) : (c == ' ') = false ∧ (c == '\n') = false ∧
    (c == '-') = false := by
  have h' := h
  unfold Char.isDigit at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le] at h'
  refine ⟨?_, ?_, ?_⟩ <;> (rw [beq_eq_false_iff_ne]; rintro rfl; revert h'; decide)

theorem preOK_sep {p : List Char} {st sg v : Nat} (h : PreOK p st sg v) :
    ∀ y ∈ p, (y == ' ') = false ∧ (y == '\n') = false := by
  rcases h with ⟨-, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, ds, -, hd, -, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩
  · intro y hy
    cases hy
  · intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    decide
  · intro y hy
    exact ⟨(digit_ne (hd y hy)).1, (digit_ne (hd y hy)).2.1⟩
  · intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · decide
    · exact ⟨(digit_ne (hd y hy)).1, (digit_ne (hd y hy)).2.1⟩

theorem tv_preOK {p : List Char} {sg v : Nat} (h : PreOK p 2 sg v) : tv p = some (tokV sg v) := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ds, hne, hd, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rw [tv_pos hd hne, hv]
    rfl
  · rw [tv_neg hd hne, hv]
    rfl

theorem lineW_tok {p : List Char} {sg v : Nat} (h : PreOK p 2 sg v) (r : List Char) :
    lineW (p ++ ' ' :: r) = tokV sg v :: lineW r := by
  unfold lineW
  rw [List.splitOnP_append_cons_of_forall_mem (fun y hy => (preOK_sep h y hy).1) ' ' (by decide),
    List.filterMap_cons, tv_preOK h]

theorem lineW_last {p : List Char} {sg v : Nat} (h : PreOK p 2 sg v) : lineW p = [tokV sg v] := by
  unfold lineW
  rw [List.splitOnP_eq_singleton (fun y hy => (preOK_sep h y hy).1), List.filterMap_cons,
    tv_preOK h, List.filterMap_nil]

theorem lineW_nil : lineW [] = [] := by
  unfold lineW
  rw [List.splitOnP_nil, List.filterMap_cons, tv_nil, List.filterMap_nil]

theorem splitNl_cons {c : Char} (hc : (c == '\n') = false) (cs : List Char) :
    List.splitOnP (· == '\n') (c :: cs) =
      (c :: (List.splitOnP (· == '\n') cs).headD []) :: (List.splitOnP (· == '\n') cs).tail := by
  rw [List.splitOnP_cons_eq_ite_modifyHead, ite_eq_right (by simpa using hc)]
  obtain ⟨a, l, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') cs)
  rw [e]
  rfl

theorem splitNl_nl (cs : List Char) :
    List.splitOnP (· == '\n') ('\n' :: cs) = [] :: List.splitOnP (· == '\n') cs := by
  rw [List.splitOnP_cons_eq_ite_modifyHead, ite_eq_left (by decide)]

theorem textW_cons_nonempty {c : Char} {l : List Char} (ls : List (List Char)) :
    textW ((c :: l) :: ls) = lineW (c :: l) :: textW ls := by
  simp [textW]

theorem textW_cons_nil (ls : List (List Char)) : textW ([] :: ls) = textW ls := by
  simp [textW]

theorem digV_lt {c : Nat} (h : Nat.blt (digV c) 10 = true) : 48 ≤ c ∧ c ≤ 57 ∧ digV c = c - 48 := by
  have e : ∀ a b, Nat.ble a b = decide (a ≤ b) := fun a b =>
    Bool.eq_iff_iff.2 (by rw [Nat.ble_eq, decide_eq_true_eq])
  have hd : digV c = if 48 ≤ c ∧ c ≤ 57 then c - 48 else 10 := by
    unfold digV
    rw [e, e]
    by_cases h1 : 48 ≤ c <;> by_cases h2 : c ≤ 57 <;> simp [h1, h2] <;> rfl
  rw [hd] at h ⊢
  by_cases hc : 48 ≤ c ∧ c ≤ 57
  · rw [ite_eq_left hc]
    exact ⟨hc.1, hc.2, rfl⟩
  · rw [ite_eq_right hc] at h
    exact absurd h (by decide)

theorem isDigit_of' {c : Char} (h : 48 ≤ c.toNat ∧ c.toNat ≤ 57) : c.isDigit = true :=
  isDigit_of (by rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]; exact h)

theorem nilB_eq {α : Type} (L : List α) : nilB L = L.isEmpty := by
  cases L <;> rfl

theorem pop_spec {α : Type} {L : List α} {X : α → List α → Bool}
    (h : List.rec (motive := fun _ => Bool) false (fun W' L' _ => X W' L') L = true) :
    ∃ W' L', L = W' :: L' ∧ X W' L' = true := by
  cases L with
  | nil => exact absurd h Bool.false_ne_true
  | cons W' L' => exact ⟨W', L', rfl, h⟩

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem preOK_zero {p : List Char} {sg v : Nat} (h : PreOK p 0 sg v) : p = [] := by
  rcases h with ⟨-, hp⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hp
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)

theorem ofDigit_single (c : Char) : Nat.ofDigitChars 10 [c] 0 = c.toNat - 48 := by
  rw [Nat.ofDigitChars_eq_foldl, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
  rfl

theorem preOK_digit {p : List Char} {st sg v : Nat} (hp : PreOK p st sg v) (hst : st ≠ 0)
    {c : Char} (hc : c.isDigit = true) :
    PreOK (p ++ [c]) 2 sg (Nat.add (Nat.mul v 10) (c.toNat - 48)) := by
  rcases hp with ⟨h1, -⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, ds, hne, hd, rfl, hs⟩
  · exact absurd h1 hst
  · refine Or.inr (Or.inr ⟨rfl, [c], by simp, by simpa using hc, ?_, Or.inr ⟨rfl, rfl⟩⟩)
    rw [ofDigit_single]
    simp
  · refine Or.inr (Or.inr ⟨rfl, ds ++ [c], by simp, fun y hy => ?_, ?_, ?_⟩)
    · rcases List.mem_append.1 hy with hy | hy
      · exact hd y hy
      · rw [List.mem_singleton] at hy
        subst hy
        exact hc
    · rw [ofDigitChars_snoc]
      rfl
    · rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

theorem preOK_first {c : Char} (hc : c.isDigit = true) : PreOK [c] 2 0 (c.toNat - 48) :=
  Or.inr (Or.inr ⟨rfl, [c], by simp, by simpa using hc, (ofDigit_single c).symm,
    Or.inl ⟨rfl, rfl⟩⟩)

theorem run_inv : ∀ (cs : List Char) (L : List (List Int)) (W : List Int) (st sg v ln : Nat)
    (p : List Char), PreOK p st sg v → (ln = 0 ∨ ln = 1) → (st ≠ 0 → ln = 1) → (ln = 0 → W = []) →
    wordsRunT cs L W st sg v ln = true →
    (ln = 1 → lineW (p ++ (List.splitOnP (· == '\n') cs).headD []) = W ∧
      textW (List.splitOnP (· == '\n') cs).tail = L) ∧
    (ln = 0 → textW (List.splitOnP (· == '\n') cs) = L)
  | [], L, W, st, sg, v, ln, p, hp, hln, hst, hW, h => by
    change Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq st 2) = true at h
    rw [List.splitOnP_nil]
    simp only [List.headD_cons, List.tail_cons, List.append_nil]
    cases h2 : Nat.beq st 2
    · rw [h2] at h
      dsimp only at h
      rw [bAnd_eqT, bAnd_eqT, Bool.and_eq_true, Bool.and_eq_true, nilB_eq, nilB_eq,
        List.isEmpty_iff, List.isEmpty_iff] at h
      obtain ⟨h0, rfl, rfl⟩ := h
      have hst0 : st = 0 := Nat.eq_of_beq_eq_true h0
      have hp0 : p = [] := by
        rcases hp with ⟨-, hp⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hp
        · omega
        · omega
      subst hp0
      exact ⟨fun _ => ⟨lineW_nil, rfl⟩, fun _ => by simp [textW]⟩
    · rw [h2] at h
      dsimp only at h
      have hst2 : st = 2 := Nat.eq_of_beq_eq_true h2
      subst hst2
      cases W with
      | nil => exact absurd h Bool.false_ne_true
      | cons x xs =>
        change Bool.rec (motive := fun _ => Bool) false _ (decide (x = tokV sg v)) = true at h
        rw [bAnd_eqT, bAnd_eqT, Bool.and_eq_true, Bool.and_eq_true, nilB_eq, nilB_eq,
          List.isEmpty_iff, List.isEmpty_iff, decide_eq_true_eq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hl1 := hst (by decide)
        refine ⟨fun _ => ⟨lineW_last hp, rfl⟩, fun h0 => absurd (h0.symm.trans hl1) (by decide)⟩
  | ch :: cs, L, W, st, sg, v, ln, p, hp, hln, hst, hW, h => by
    unfold wordsRunT at h
    dsimp only at h
    rw [strictB_eqM] at h
    cases hd : Nat.blt (digV ch.toNat) 10
    · rw [hd] at h
      dsimp only at h
      cases hm : Nat.beq ch.toNat 45
      · rw [hm] at h
        dsimp only at h
        cases hs : Nat.beq ch.toNat 32
        · rw [hs] at h
          dsimp only at h
          cases hn : Nat.beq ch.toNat 10
          · rw [hn] at h
            exact absurd h Bool.false_ne_true
          · rw [hn] at h
            dsimp only at h
            have hch : ch = Char.ofNat 10 := char_of_beq hn (by decide)
            subst hch
            rw [splitNl_nl]
            simp only [List.headD_cons, List.tail_cons, List.append_nil]
            cases h2 : Nat.beq st 2
            · rw [h2] at h
              dsimp only at h
              rw [bAnd_eqT, bAnd_eqT, Bool.and_eq_true, Bool.and_eq_true, nilB_eq,
                List.isEmpty_iff] at h
              obtain ⟨h0, rfl, hr⟩ := h
              have hst0 := beq_true h0
              subst hst0
              have hp0 := preOK_zero hp
              subst hp0
              have ih := (run_inv cs L [] 0 0 0 0 [] (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
                (fun h => absurd rfl h) (fun _ => rfl) hr).2 rfl
              refine ⟨fun _ => ⟨lineW_nil, ih⟩, fun _ => ?_⟩
              rw [textW_cons_nil]
              exact ih
            · rw [h2] at h
              dsimp only at h
              have hst2 := beq_true h2
              subst hst2
              obtain ⟨x, xs, rfl, hx⟩ := pop_spec h
              rw [bAnd_eqT, bAnd_eqT, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
                nilB_eq, List.isEmpty_iff] at hx
              obtain ⟨rfl, rfl, hr⟩ := hx
              have ih := (run_inv cs L [] 0 0 0 0 [] (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
                (fun h => absurd rfl h) (fun _ => rfl) hr).2 rfl
              have hl1 := hst (by decide)
              exact ⟨fun _ => ⟨lineW_last hp, ih⟩, fun h0 => absurd (h0.symm.trans hl1) (by decide)⟩
        · rw [hs] at h
          dsimp only at h
          have hch : ch = Char.ofNat 32 := char_of_beq hs (by decide)
          subst hch
          rw [bAnd_eqT, Bool.and_eq_true] at h
          obtain ⟨h2, h⟩ := h
          have hst2 := beq_true h2
          subst hst2
          obtain ⟨x, xs, rfl, hx⟩ := pop_spec h
          rw [bAnd_eqT, Bool.and_eq_true, decide_eq_true_eq] at hx
          obtain ⟨rfl, hr⟩ := hx
          have hl1 := hst (by decide)
          have ih := (run_inv cs L xs 0 0 0 1 [] (Or.inl ⟨rfl, rfl⟩) (Or.inr rfl) (fun _ => rfl)
            (fun h => absurd h (by decide)) hr).1 rfl
          rw [splitNl_cons (by decide)]
          simp only [List.headD_cons, List.tail_cons]
          refine ⟨fun _ => ⟨?_, ih.2⟩, fun h0 => absurd (h0.symm.trans hl1) (by decide)⟩
          rw [lineW_tok hp, ← ih.1, List.nil_append]
      · rw [hm] at h
        dsimp only at h
        have hch : ch = Char.ofNat 45 := char_of_beq hm (by decide)
        subst hch
        rw [bAnd_eqT, Bool.and_eq_true] at h
        obtain ⟨h0, h⟩ := h
        have hst0 := beq_true h0
        subst hst0
        have hp0 := preOK_zero hp
        subst hp0
        have hpm : PreOK [Char.ofNat 45] 1 1 0 := Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
        rw [splitNl_cons (by decide)]
        simp only [List.headD_cons, List.tail_cons]
        cases hl : Nat.beq ln 0
        · rw [hl] at h
          dsimp only at h
          have hl1 : ln = 1 := by
            have := beq_false hl
            omega
          subst hl1
          have ih := (run_inv cs L W 1 1 0 1 _ hpm (Or.inr rfl) (fun _ => rfl)
            (fun h => absurd h (by decide)) h).1 rfl
          refine ⟨fun _ => ⟨?_, ih.2⟩, fun h0 => absurd h0 (by decide)⟩
          rw [List.nil_append, ← ih.1]
          rfl
        · rw [hl] at h
          dsimp only at h
          have hl0 := beq_true hl
          subst hl0
          obtain ⟨W', L', rfl, hr⟩ := pop_spec h
          have ih := (run_inv cs L' W' 1 1 0 1 _ hpm (Or.inr rfl) (fun _ => rfl)
            (fun h => absurd h (by decide)) hr).1 rfl
          refine ⟨fun h1 => absurd h1 (by decide), fun _ => ?_⟩
          rw [textW_cons_nonempty, ih.2, ← ih.1]
          rfl
    · rw [hd] at h
      dsimp only at h
      obtain ⟨d1, d2, d3⟩ := digV_lt hd
      have hdig : ch.isDigit = true := isDigit_of' ⟨d1, d2⟩
      rw [d3] at h
      rw [splitNl_cons (digit_ne hdig).2.1]
      simp only [List.headD_cons, List.tail_cons]
      cases h0 : Nat.beq st 0
      · rw [h0] at h
        dsimp only at h
        have hst0 := beq_false h0
        have hl1 := hst hst0
        subst hl1
        have ih := (run_inv cs L W 2 sg _ 1 _ (preOK_digit hp hst0 hdig) (Or.inr rfl) (fun _ => rfl)
          (fun h => absurd h (by decide)) h).1 rfl
        refine ⟨fun _ => ⟨?_, ih.2⟩, fun h => absurd h (by decide)⟩
        rw [← ih.1, List.append_assoc]
        rfl
      · rw [h0] at h
        dsimp only at h
        have hst0 := beq_true h0
        subst hst0
        have hp0 := preOK_zero hp
        subst hp0
        cases hl : Nat.beq ln 0
        · rw [hl] at h
          dsimp only at h
          have hl1 : ln = 1 := by
            have := beq_false hl
            omega
          subst hl1
          have ih := (run_inv cs L W 2 0 _ 1 _ (preOK_first hdig) (Or.inr rfl) (fun _ => rfl)
            (fun h => absurd h (by decide)) h).1 rfl
          refine ⟨fun _ => ⟨?_, ih.2⟩, fun h => absurd h (by decide)⟩
          rw [List.nil_append, ← ih.1]
          rfl
        · rw [hl] at h
          dsimp only at h
          have hl0 := beq_true hl
          subst hl0
          obtain ⟨W', L', rfl, hr⟩ := pop_spec h
          have ih := (run_inv cs L' W' 2 0 _ 1 _ (preOK_first hdig) (Or.inr rfl) (fun _ => rfl)
            (fun h => absurd h (by decide)) hr).1 rfl
          refine ⟨fun h1 => absurd h1 (by decide), fun _ => ?_⟩
          rw [textW_cons_nonempty, ih.2, ← ih.1]
          rfl

theorem wordsT_sound {cs : List Char} {L : List (List Int)} (h : wordsT cs L = true) :
    CFSG.Sporadic.Bridge.SuzGPL.Native.parseWords (String.ofList cs) = L.toArray := by
  change Bool.rec (motive := fun _ => Bool) false _ _ = true at h
  rw [bAnd_eqT, Bool.and_eq_true] at h
  have hr := (run_inv cs L [] 0 0 0 0 [] (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl) (fun h => absurd rfl h)
    (fun _ => rfl) h.2).2 rfl
  unfold CFSG.Sporadic.Bridge.SuzGPL.Native.parseWords
  rw [splitOn_nl, List.splitOnPPrepend_nil_right, ← hr]
  congr 1
  unfold textW
  rw [List.filter_map, List.map_map]
  have e1 : ((fun l : String => !l.isEmpty) ∘ String.ofList) = fun l : List Char => !l.isEmpty := by
    funext l
    simp only [Function.comp_apply]
    cases l with
    | nil => rfl
    | cons c l =>
      have : (String.ofList (c :: l)).isEmpty = false := by
        rw [Bool.eq_false_iff]
        intro he
        rw [String.isEmpty_iff] at he
        have := congrArg String.toList he
        simp at this
      rw [this]
      rfl
  rw [e1]
  congr 1
  funext l
  simp only [Function.comp_apply, CFSG.Sporadic.Bridge.SuzGPL.Native.parseLine, lineW]
  rw [splitOn_sp, List.splitOnPPrepend_nil_right, List.filterMap_map]
  rfl

end CFSG.KC.WordsT

end
