module

public import Certificates.Data.Kernel.J4Q.QT
public import CFSG.Certificates.Kernel.J4Q.Rep
public import CFSG.Sporadic.J4.QTNative
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Batteries.Data.String.Lemmas

public section

namespace CFSG.KC.J4Q

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.KC.Loop

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem letOf_spec (ch : Char) :
    (if ch = 'a' then some (1 : Int) else if ch = 'b' then some 2 else if ch = 'c' then some 3
      else if ch = 'A' then some (-1) else if ch = 'B' then some (-2) else if ch = 'C' then some (-3)
      else none) =
    Bool.rec (motive := fun _ => Option Int) none (some (letOf ch.toNat)) (isLet ch.toNat) := by
  have key : ∀ (d : Char), ch = d ↔ ch.toNat = d.toNat := fun _ => Char.toNat_inj.symm
  by_cases ha : ch.toNat = 97
  · have : ch = 'a' := (key 'a').2 ha
    subst this
    rfl
  by_cases hb : ch.toNat = 98
  · have : ch = 'b' := (key 'b').2 hb
    subst this
    rfl
  by_cases hc : ch.toNat = 99
  · have : ch = 'c' := (key 'c').2 hc
    subst this
    rfl
  by_cases hA : ch.toNat = 65
  · have : ch = 'A' := (key 'A').2 hA
    subst this
    rfl
  by_cases hB : ch.toNat = 66
  · have : ch = 'B' := (key 'B').2 hB
    subst this
    rfl
  by_cases hC : ch.toNat = 67
  · have : ch = 'C' := (key 'C').2 hC
    subst this
    rfl
  have h1 : ch ≠ 'a' := fun h => ha ((key _).1 h)
  have h2 : ch ≠ 'b' := fun h => hb ((key _).1 h)
  have h3 : ch ≠ 'c' := fun h => hc ((key _).1 h)
  have h4 : ch ≠ 'A' := fun h => hA ((key _).1 h)
  have h5 : ch ≠ 'B' := fun h => hB ((key _).1 h)
  have h6 : ch ≠ 'C' := fun h => hC ((key _).1 h)
  have hl : isLet ch.toNat = false := by
    unfold isLet
    rw [nbeq_false ha, nbeq_false hb, nbeq_false hc, nbeq_false hA, nbeq_false hB, nbeq_false hC]
    rfl
  rw [hl]
  simp [h1, h2, h3, h4, h5, h6]

theorem lettersOfString_ofList (cs : List Char) :
    lettersOfString (String.ofList cs) = lettersK cs := by
  unfold lettersOfString
  rw [String.toList_ofList]
  induction cs with
  | nil => rfl
  | cons ch cs ih =>
    rw [List.filterMap_cons, letOf_spec ch, ih]
    change _ = Bool.rec (motive := fun _ => List Int) (lettersK cs)
      (List.cons (letOf ch.toNat) (lettersK cs)) (isLet ch.toNat)
    cases isLet ch.toNat <;> rfl

section Split

open String

private theorem sp_get0 : Pos.Raw.get " " 0 = ' ' := rfl
private theorem sp_next0 : Pos.Raw.next " " 0 = ⟨1⟩ := rfl

private theorem splitOnAux_sp (l m r : List Char) (acc : List String) :
    String.splitOnAux (String.ofList (l ++ m ++ r)) " " ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == ' ') r m.reverse).map String.ofList := by
  unfold String.splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons, sp_get0, sp_next0]
  have hend : " ".rawEndPos ≤ (⟨1⟩ : Pos.Raw) := by decide
  have hz : ∀ p : Pos.Raw, p.unoffsetBy 0 = p := fun ⟨n⟩ => by simp [Pos.Raw.unoffsetBy]
  simp only [hend, ↓reduceIte, hz]
  split
  · subst r
    simpa using extract_of_valid l m []
  · obtain ⟨c, r, rfl⟩ := r.exists_cons_of_ne_nil ‹_›
    simp only [by
      simpa [-ofList_append] using
        (⟨get_of_valid (l ++ m) (c :: r), next_of_valid (l ++ m) c r,
            extract_of_valid l m (c :: r)⟩ :
          _ ∧ _ ∧ _)]
    split <;> rename_i h
    · have hc : c = ' ' := by simpa using h
      subst hc
      have hu : utf8Len l + (utf8Len m + ' '.utf8Size) - 1 = utf8Len l + utf8Len m := by
        have : ' '.utf8Size = 1 := rfl
        omega
      have hx := extract_of_valid l m (' ' :: r)
      simp at hx
      simpa [Pos.Raw.unoffsetBy, hu, hx, Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_sp (l ++ m ++ [' ']) [] r ((ofList m) :: acc)
    · simpa [Pos.Raw.unoffsetBy, List.splitOnPPrepend_cons_eq_ite, h, Nat.add_assoc] using
        splitOnAux_sp l (m ++ [c]) r acc

private theorem splitOn_sp (cs : List Char) :
    (String.ofList cs).splitOn " " = (List.splitOnPPrepend (· == ' ') cs []).map String.ofList := by
  have h := splitOnAux_sp [] [] cs []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil] at h
  unfold String.splitOn
  have hne : (" " == "") = false := by decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact h

end Split

private theorem forIn_yield {L : List Char}
    {f : Char → Option Bool × Bool → Id (ForInStep (Option Bool × Bool))}
    (hf : ∀ c ∈ L, ∀ s, f c s = pure (.yield (none, true))) :
    ∀ s, forIn L s f = pure (if L = [] then s else (none, true)) := by
  induction L with
  | nil => intro s; rfl
  | cons c L ih =>
    intro s
    rw [List.forIn_cons, hf c List.mem_cons_self s]
    change forIn L (none, true) f = _
    rw [ih (fun c hc s => hf c (List.mem_cons_of_mem _ hc) s)]
    simp

private theorem digit_ne {c : Char} (h : c.isDigit = true) : c ≠ '_' := by
  rintro rfl
  exact absurd h (by decide)

private theorem isNat_digits (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (String.ofList ds).toSlice.isNat = !ds.isEmpty := by
  unfold String.Slice.isNat
  simp only [String.Slice.forIn_eq_forIn_toList, String.copy_toSlice, String.toList_ofList]
  rw [forIn_yield]
  · cases ds <;> rfl
  · intro c hc s
    simp [digit_ne (hd c hc), hd c hc]

private theorem foldl_digits : ∀ (L : List Char) (acc : Nat), (∀ c ∈ L, c.isDigit = true) →
    L.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) acc =
      L.foldl (fun n c => n * 10 + (c.toNat - 48)) acc
  | [], _, _ => rfl
  | c :: L, acc, h => by
    rw [List.foldl_cons, List.foldl_cons, ite_eq_right (digit_ne (h c List.mem_cons_self))]
    exact foldl_digits L _ fun c hc => h c (List.mem_cons_of_mem _ hc)

private theorem digVal (ds : List Char) (hd : ∀ c ∈ ds, c.isDigit = true) :
    (String.ofList ds).toNat?.getD 0 = ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0 := by
  unfold String.toNat? String.Slice.toNat?
  rw [isNat_digits ds hd]
  cases ds with
  | nil => rfl
  | cons c L =>
    simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte, Option.getD_some,
      String.Slice.foldl_eq_foldl_toList, String.copy_toSlice, String.toList_ofList]
    exact foldl_digits (c :: L) 0 hd

private theorem andB_eq_and (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

private theorem isDig_eq (c : Char) : isDig c.toNat = c.isDigit := by
  unfold isDig Char.isDigit
  apply Bool.eq_iff_iff.mpr
  simp only [andB_eq_and, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq, ge_iff_le,
    UInt32.le_iff_toNat_le]
  rfl

private theorem ofList_isEmpty (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  cases p <;> simp [String.isEmpty_iff]

private noncomputable def nOf (cur : List Char) : Nat :=
  (cur.takeWhile Char.isDigit).foldl (fun n c => n * 10 + (c.toNat - 48)) 0

private theorem lettersK_append (L : List Char) (ch : Char) :
    lettersK (L ++ [ch]) = lettersK L ++ (if isLet ch.toNat then [letOf ch.toNat] else []) := by
  induction L with
  | nil =>
    change Bool.rec (motive := fun _ => List Int) [] [letOf ch.toNat] (isLet ch.toNat) = _
    cases isLet ch.toNat <;> rfl
  | cons c L ih =>
    change Bool.rec (motive := fun _ => List Int) (lettersK (L ++ [ch]))
      (letOf c.toNat :: lettersK (L ++ [ch])) (isLet c.toNat) =
      Bool.rec (motive := fun _ => List Int) (lettersK L) (letOf c.toNat :: lettersK L)
        (isLet c.toNat) ++ _
    rw [ih]
    cases isLet c.toNat <;> rfl

private theorem revOnto_nil {α : Type} : ∀ (l acc : List α), revOnto l acc = l.reverse ++ acc
  | [], _ => rfl
  | x :: l, acc => by
    change revOnto l (x :: acc) = _
    rw [revOnto_nil l, List.reverse_cons, List.append_assoc]
    rfl

private noncomputable def tokOf (p : List Char) : Option (Nat × List Int) :=
  if p = [] then none else some (nOf p, lettersK (p.dropWhile Char.isDigit))

private theorem ptsGo_eq : ∀ (cs cur : List Char),
    ptsGo cs (cur.all Char.isDigit) (nOf cur) (!cur.isEmpty)
        (lettersK (cur.dropWhile Char.isDigit)).reverse =
      (List.splitOnPPrepend (· == ' ') cs cur.reverse).filterMap tokOf
  | [], cur => by
    rw [List.splitOnPPrepend_nil, List.reverse_reverse]
    change Bool.rec (motive := fun _ => List (Nat × List Int)) [] _ (!cur.isEmpty) = _
    unfold tokOf
    cases cur with
    | nil => rfl
    | cons c L =>
      simp only [List.isEmpty_cons, Bool.not_false, List.filterMap_cons, List.filterMap_nil,
        reduceCtorEq, ↓reduceIte]
      rw [revOnto_nil, List.reverse_reverse, List.append_nil]
  | ch :: cs, cur => by
    by_cases hs : ch = ' '
    · subst hs
      rw [List.splitOnPPrepend_cons_eq_ite]
      simp only [beq_self_eq_true, ↓reduceIte, List.reverse_reverse, List.filterMap_cons]
      have e := ptsGo_eq cs []
      simp only [List.all_nil, List.isEmpty_nil, Bool.not_true, List.dropWhile_nil, List.reverse_nil,
        List.splitOnPPrepend_nil_right] at e
      change Bool.rec (motive := fun _ => List (Nat × List Int))
        (ptsGo cs true 0 false [])
        ((nOf cur, revOnto (lettersK (cur.dropWhile Char.isDigit)).reverse []) ::
          ptsGo cs true 0 false [])
        (!cur.isEmpty) = _
      have hn : nOf [] = 0 := rfl
      have hl : lettersK [] = [] := rfl
      rw [hn, hl, List.reverse_nil] at e
      rw [e, List.splitOnP_eq_splitOnPPrepend]
      unfold tokOf
      cases cur with
      | nil => rfl
      | cons c L =>
        simp only [List.isEmpty_cons, Bool.not_false, reduceCtorEq, ↓reduceIte]
        rw [revOnto_nil, List.reverse_reverse, List.append_nil]
    · rw [List.splitOnPPrepend_cons_eq_ite]
      have hb : (ch == ' ') = false := by simpa using hs
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hk : Nat.beq ch.toNat 32 = false := by
        cases h : Nat.beq ch.toNat 32
        · rfl
        · exfalso
          apply hs
          exact Char.ext (UInt32.toNat_inj.mp (by simpa using Nat.eq_of_beq_eq_true h))
      have e := ptsGo_eq cs (cur ++ [ch])
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at e
      rw [← e]
      change Bool.rec (motive := fun _ => List (Nat × List Int)) _ _ (Nat.beq ch.toNat 32) = _
      rw [hk]
      change Bool.rec (motive := fun _ => List (Nat × List Int)) _ _
        (andB (cur.all Char.isDigit) (isDig ch.toNat)) = _
      rw [isDig_eq, andB_eq_and]
      have hne : (!(cur ++ [ch]).isEmpty) = true := by simp
      rw [hne]
      by_cases hd : cur.all Char.isDigit = true
      · have hcur : cur.dropWhile Char.isDigit = [] := List.dropWhile_eq_nil_iff.2 (by simpa using hd)
        have htw : cur.takeWhile Char.isDigit = cur := List.takeWhile_eq_self_iff.2 (by simpa using hd)
        by_cases hc : ch.isDigit = true
        · rw [hd, hc]
          have hall : (cur ++ [ch]).all Char.isDigit = true := by simp_all
          rw [hall]
          have hdw : (cur ++ [ch]).dropWhile Char.isDigit = [] :=
            List.dropWhile_eq_nil_iff.2 (List.all_eq_true.1 hall)
          have htw' : (cur ++ [ch]).takeWhile Char.isDigit = cur ++ [ch] :=
            List.takeWhile_eq_self_iff.2 (List.all_eq_true.1 hall)
          rw [hdw, hcur]
          unfold nOf
          rw [htw, htw', List.foldl_append]
          rfl
        · have hc' : ch.isDigit = false := by simpa using hc
          rw [hd, hc']
          have hall : (cur ++ [ch]).all Char.isDigit = false := by simp [hc']
          rw [hall]
          have hdw : (cur ++ [ch]).dropWhile Char.isDigit = [ch] := by
            rw [List.dropWhile_append, hcur]
            simp [hc']
          have htw' : (cur ++ [ch]).takeWhile Char.isDigit = cur := by
            rw [List.takeWhile_append, htw]
            simp [hc']
          rw [hdw, hcur]
          unfold nOf
          rw [htw, htw']
          change _ = ptsGo cs false _ true (lettersK ([] ++ [ch])).reverse
          rw [lettersK_append]
          change ptsGo cs false _ true (Bool.rec (motive := fun _ => List Int) [] _ _) = _
          cases isLet ch.toNat <;> rfl
      · have hd' : cur.all Char.isDigit = false := by simpa using hd
        rw [hd']
        have hall : (cur ++ [ch]).all Char.isDigit = false := by simp [hd']
        rw [hall]
        obtain ⟨x, hx, hxd⟩ : ∃ x ∈ cur, x.isDigit = false := by simpa using hd'
        have hne' : (cur.dropWhile Char.isDigit).isEmpty = false := by
          cases h : cur.dropWhile Char.isDigit with
          | nil =>
            rw [List.dropWhile_eq_nil_iff] at h
            rw [h x hx] at hxd
            exact Bool.noConfusion hxd
          | cons _ _ => rfl
        have hdw : (cur ++ [ch]).dropWhile Char.isDigit = cur.dropWhile Char.isDigit ++ [ch] := by
          rw [List.dropWhile_append, hne']
          rfl
        have htw' : (cur ++ [ch]).takeWhile Char.isDigit = cur.takeWhile Char.isDigit := by
          rw [List.takeWhile_append]
          split
          · rename_i h
            exfalso
            have hself := List.IsPrefix.eq_of_length (List.takeWhile_prefix _) h
            rw [List.takeWhile_eq_self_iff] at hself
            rw [hself x hx] at hxd
            exact Bool.noConfusion hxd
          · rfl
        unfold nOf
        rw [hdw, htw', lettersK_append]
        change ptsGo cs false _ true (Bool.rec (motive := fun _ => List Int) _ _ _) = _
        cases isLet ch.toNat <;> simp

theorem ptsOfString_ofList (cs : List Char) : ptsOfString (String.ofList cs) = ptsK cs := by
  unfold ptsOfString ptsK
  rw [splitOn_sp, List.filterMap_map]
  have e := ptsGo_eq cs []
  simp only [List.all_nil, List.isEmpty_nil, Bool.not_true, List.dropWhile_nil, List.reverse_nil] at e
  have hn : nOf [] = 0 := rfl
  have hl : lettersK [] = [] := rfl
  rw [hn, hl, List.reverse_nil] at e
  rw [e]
  congr 1
  funext p
  unfold tokOf nOf
  simp only [Function.comp_apply, ofList_isEmpty, String.toList_ofList, lettersOfString_ofList]
  cases p with
  | nil => rfl
  | cons c L =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
    rw [digVal _ (fun c hc => List.mem_takeWhile_imp hc)]

private noncomputable def idxOf (p : List Char) : Option (List Nat) :=
  if p = [] then none else if p = ['_'] then some [] else some (p.map fun ch => ch.toNat - 97)

private theorem idxGo_eq : ∀ (cs cur : List Char),
    idxGo cs (min cur.length 2) (cur == ['_']) (cur.map fun ch => ch.toNat - 97).reverse =
      (List.splitOnPPrepend (· == ' ') cs cur.reverse).filterMap idxOf
  | [], cur => by
    rw [List.splitOnPPrepend_nil, List.reverse_reverse]
    cases cur with
    | nil => rfl
    | cons c L =>
      have hm : Nat.beq (min (c :: L).length 2) 0 = false := nbeq_false (by rw [List.length_cons]; omega)
      change Bool.rec (motive := fun _ => List (List Nat))
        [Bool.rec (motive := fun _ => List Nat)
          (revOnto ((c :: L).map fun ch => ch.toNat - 97).reverse []) [] ((c :: L) == ['_'])] []
        (Nat.beq (min (c :: L).length 2) 0) = _
      rw [hm, revOnto_nil, List.reverse_reverse, List.append_nil]
      unfold idxOf
      by_cases h : c :: L = ['_']
      · rw [h]
        rfl
      · have hb : ((c :: L) == ['_']) = false := by simpa using h
        rw [hb]
        simp [h]
  | ch :: cs, cur => by
    by_cases hs : ch = ' '
    · subst hs
      rw [List.splitOnPPrepend_cons_eq_ite]
      simp only [beq_self_eq_true, ↓reduceIte, List.reverse_reverse, List.filterMap_cons]
      have e := idxGo_eq cs []
      simp only [List.length_nil, List.reverse_nil, List.map_nil, List.splitOnPPrepend_nil_right] at e
      have h0 : min 0 2 = 0 := rfl
      have hf : (([] : List Char) == ['_']) = false := rfl
      rw [h0, hf] at e
      change Bool.rec (motive := fun _ => List (List Nat))
        ((Bool.rec (motive := fun _ => List Nat)
          (revOnto (cur.map fun ch => ch.toNat - 97).reverse []) [] (cur == ['_'])) ::
            idxGo cs 0 false [])
        (idxGo cs 0 false []) (Nat.beq (min cur.length 2) 0) = _
      rw [e, List.splitOnP_eq_splitOnPPrepend, revOnto_nil, List.reverse_reverse, List.append_nil]
      unfold idxOf
      cases cur with
      | nil => rfl
      | cons c L =>
        have hm : Nat.beq (min (c :: L).length 2) 0 = false :=
          nbeq_false (by rw [List.length_cons]; omega)
        rw [hm]
        by_cases h : c :: L = ['_']
        · rw [h]
          rfl
        · have hb : ((c :: L) == ['_']) = false := by simpa using h
          rw [hb]
          simp [h]
    · rw [List.splitOnPPrepend_cons_eq_ite]
      have hb : (ch == ' ') = false := by simpa using hs
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hk : Nat.beq ch.toNat 32 = false := by
        cases h : Nat.beq ch.toNat 32
        · rfl
        · exfalso
          apply hs
          exact Char.ext (UInt32.toNat_inj.mp (by simpa using Nat.eq_of_beq_eq_true h))
      have e := idxGo_eq cs (cur ++ [ch])
      rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at e
      rw [← e]
      have h1 : min (cur ++ [ch]).length 2 =
          Bool.rec (motive := fun _ => Nat) 2 1 (Nat.beq (min cur.length 2) 0) := by
        cases cur with
        | nil => rfl
        | cons c L =>
          rw [nbeq_false (by rw [List.length_cons]; omega)]
          change _ = 2
          rw [List.length_append, List.length_cons, List.length_singleton]
          omega
      have h2 : ((cur ++ [ch]) == ['_']) =
          andB (Nat.beq (min cur.length 2) 0) (Nat.beq ch.toNat 95) := by
        cases cur with
        | nil =>
          change ([ch] == ['_']) = Nat.beq ch.toNat 95
          apply Bool.eq_iff_iff.mpr
          rw [beq_iff_eq, Nat.beq_eq]
          constructor
          · intro h
            simp only [List.cons.injEq, and_true] at h
            rw [h]
            rfl
          · intro h
            have : ch = '_' := Char.ext (UInt32.toNat_inj.mp (by simpa using h))
            rw [this]
        | cons c L =>
          rw [nbeq_false (by rw [List.length_cons]; omega)]
          change _ = false
          simp
      rw [h1, h2, List.map_append, List.reverse_append]
      change Bool.rec (motive := fun _ => List (List Nat)) _ _ (Nat.beq ch.toNat 32) = _
      rw [hk]
      rfl

theorem idxWordsOfString_ofList (cs : List Char) :
    idxWordsOfString (String.ofList cs) = idxK cs := by
  unfold idxWordsOfString idxK
  rw [splitOn_sp, List.filterMap_map]
  have e := idxGo_eq cs []
  simp only [List.length_nil, List.reverse_nil, List.map_nil] at e
  have h0 : min 0 2 = 0 := rfl
  have hf : (([] : List Char) == ['_']) = false := rfl
  rw [h0, hf] at e
  rw [e]
  congr 1
  funext p
  unfold idxOf
  simp only [Function.comp_apply, ofList_isEmpty, String.toList_ofList]
  cases p with
  | nil => rfl
  | cons c L =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
    have hu : (String.ofList (c :: L) = "_") ↔ c :: L = ['_'] := by
      constructor
      · intro h
        have := congrArg String.toList h
        rw [String.toList_ofList] at this
        exact this
      · intro h
        rw [h]
    by_cases h : c :: L = ['_']
    · rw [ite_eq_left (hu.2 h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hu.1 h')), ite_eq_right h]
      rfl

theorem negRevOnto_eq : ∀ (w acc : List Int), negRevOnto w acc = (w.reverse.map fun l => -l) ++ acc
  | [], acc => rfl
  | l :: w, acc => by
    change negRevOnto w (Int.neg l :: acc) = _
    rw [negRevOnto_eq w, List.reverse_cons, List.map_append, List.append_assoc]
    rfl

theorem invWord_eq (w : List Int) : invWord w = negRev w := by
  rw [negRev, negRevOnto_eq, List.append_nil]
  rfl

theorem revOnto_eq {α : Type} : ∀ (l acc : List α), revOnto l acc = l.reverse ++ acc
  | [], acc => rfl
  | x :: l, acc => by
    change revOnto l (x :: acc) = _
    rw [revOnto_eq l, List.reverse_cons, List.append_assoc]
    rfl

theorem strictL_eq {α : Type} (y : Nat) (k : Nat → List α) : strictL y k = k y := by
  cases y <;> rfl

theorem smapRev_eq (f : Nat → Nat) : ∀ (l acc : List Nat), smapRev f l acc = (l.map f).reverse ++ acc
  | [], acc => rfl
  | x :: l, acc => by
    change strictL (f x) (fun v => smapRev f l (v :: acc)) = _
    rw [strictL_eq, smapRev_eq f l, List.map_cons, List.reverse_cons, List.append_assoc]
    rfl

theorem smapK_eq (f : Nat → Nat) (l : List Nat) : smapK f l = l.map f := by
  rw [smapK, revOnto_eq, smapRev_eq, List.append_nil, List.append_nil, List.reverse_reverse]

theorem rangeK_eq (n : Nat) : rangeK n = List.range n := by
  have h : ∀ n acc, Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons k acc)) n acc = List.range n ++ acc := by
    intro n
    induction n with
    | zero => intro acc; rfl
    | succ n ih =>
      intro acc
      change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
        (fun k ih acc => ih (List.cons k acc)) n (n :: acc) = _
      rw [ih, List.range_succ, List.append_assoc]
      rfl
  rw [rangeK, h, List.append_nil]

theorem getN_append (d : Nat) : ∀ (l1 l2 : List Nat) (k : Nat),
    getN d (l1 ++ l2) k = if k < l1.length then getN d l1 k else getN d l2 (k - l1.length)
  | [], l2, k => by simp
  | x :: l1, l2, 0 => by simp [getN]
  | x :: l1, l2, k + 1 => by
    have h := getN_append d l1 l2 k
    simp only [List.cons_append, List.length_cons]
    change getN d (l1 ++ l2) k = _
    rw [h]
    by_cases hk : k < l1.length
    · simp [hk, getN]
    · simp only [hk, ↓reduceIte, Nat.add_lt_add_iff_right, Nat.add_sub_add_right]

theorem rows_wf_of {X : Array V2} (h : WfA X) : ∀ x ∈ X, x.wf = true := by
  intro x hx
  have := h.2
  rw [Array.all_eq_true] at this
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
  exact this i hi

theorem mulRows_idRows {X : Array V2} (hX : ∀ x ∈ X, x.wf = true) : mulRows X (idRows ()) = X := by
  apply Array.ext (by simp [CFSG.Sporadic.J4.mulRows_size])
  intro i h1 h2
  simp only [mulRows, Array.getElem_map]
  apply CFSG.Sporadic.J4.Native.V2.eq_of_toVec_eq
    (CFSG.Sporadic.J4.frApply_frTable_wf CFSG.Sporadic.J4.idRows_wf _) (hX _ (Array.getElem_mem h2))
  rw [CFSG.Sporadic.J4.frApply_toVec_eq_vecMul, CFSG.Sporadic.J4.rowsMatrix_idRows, Matrix.vecMul_one]

theorem rows_ext {X Y : Array V2} (hX : WfA X) (hY : WfA Y)
    (h : CFSG.Sporadic.J4.rowsMatrix X = CFSG.Sporadic.J4.rowsMatrix Y) : X = Y := by
  apply Array.ext (hX.1.trans hY.1.symm)
  intro i h1 h2
  have hi : i < 112 := hX.1 ▸ h1
  apply CFSG.Sporadic.J4.Native.V2.eq_of_toVec_eq (rows_wf_of hX _ (Array.getElem_mem h1))
    (rows_wf_of hY _ (Array.getElem_mem h2))
  funext j
  have := congrFun (congrFun h ⟨i, hi⟩) j
  rwa [CFSG.Sporadic.J4.rowsMatrix_apply, CFSG.Sporadic.J4.rowsMatrix_apply,
    Array.getElem?_eq_getElem h1, Array.getElem?_eq_getElem h2, Option.getD_some,
    Option.getD_some] at this

theorem mulRows_assoc {X Y Z : Array V2} (hX : WfA X) (hY : WfA Y) (hZ : WfA Z) :
    mulRows (mulRows X Y) Z = mulRows X (mulRows Y Z) :=
  rows_ext (wf_mulRows (wf_mulRows hX hY) hZ) (wf_mulRows hX (wf_mulRows hY hZ)) (by
    simp only [CFSG.Sporadic.J4.rowsMatrix_mulRows, mul_assoc])

theorem idRows_mulRows {Y : Array V2} (hY : WfA Y) : mulRows (idRows ()) Y = Y :=
  rows_ext (wf_mulRows wf_idRows hY) hY (by
    rw [CFSG.Sporadic.J4.rowsMatrix_mulRows, CFSG.Sporadic.J4.rowsMatrix_idRows, one_mul])

theorem foldl_mulRows {α : Type} {L : α → Array V2} (hL : ∀ l, WfA (L l)) :
    ∀ (b : List α) (acc : Array V2), WfA acc →
      WfA (b.foldl (fun acc l => mulRows acc (L l)) acc) ∧
      b.foldl (fun acc l => mulRows acc (L l)) acc =
        mulRows acc (b.foldl (fun acc l => mulRows acc (L l)) (idRows ()))
  | [], acc, h => ⟨h, (mulRows_idRows (rows_wf_of h)).symm⟩
  | l :: b, acc, h => by
    obtain ⟨h1, h2⟩ := foldl_mulRows hL b _ (wf_mulRows h (hL l))
    obtain ⟨h3, h4⟩ := foldl_mulRows hL b _ (wf_mulRows wf_idRows (hL l))
    obtain ⟨h5, -⟩ := foldl_mulRows hL b _ wf_idRows
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, List.foldl_cons, h2, h4, idRows_mulRows (hL l),
      mulRows_assoc h (hL l) h5]

theorem wordRows_append {mats invs : Array (Array V2)}
    (hm : ∀ k : Nat, WfA (mats[k]?.getD (idRows ())))
    (hi : ∀ k : Nat, WfA (invs[k]?.getD (idRows ())))
    (a b : List Int) :
    wordRows mats invs (a ++ b) = mulRows (wordRows mats invs a) (wordRows mats invs b) := by
  have hl : ∀ l : Int, WfA (if 0 < l then mats[l.toNat - 1]?.getD (idRows ())
      else invs[(-l).toNat - 1]?.getD (idRows ())) := by
    intro l
    split
    · exact hm _
    · exact hi _
  unfold wordRows
  rw [List.foldl_append]
  exact (foldl_mulRows hl b _ (foldl_mulRows hl a _ wf_idRows).1).2

theorem wf_wordRows {mats invs : Array (Array V2)}
    (hm : ∀ k : Nat, WfA (mats[k]?.getD (idRows ())))
    (hi : ∀ k : Nat, WfA (invs[k]?.getD (idRows ()))) (w : List Int) :
    WfA (wordRows mats invs w) := by
  have hl : ∀ l : Int, WfA (if 0 < l then mats[l.toNat - 1]?.getD (idRows ())
      else invs[(-l).toNat - 1]?.getD (idRows ())) := by
    intro l
    split
    · exact hm _
    · exact hi _
  exact (foldl_mulRows hl w _ wf_idRows).1

theorem wordRows_flatMap {mats invs : Array (Array V2)}
    (hm : ∀ k : Nat, WfA (mats[k]?.getD (idRows ())))
    (hi : ∀ k : Nat, WfA (invs[k]?.getD (idRows ()))) {β : Type} (f : β → List Int) :
    ∀ L : List β, wordRows mats invs (L.flatMap f) =
      L.foldl (fun acc x => mulRows acc (wordRows mats invs (f x))) (idRows ())
  | [] => rfl
  | x :: L => by
    rw [List.flatMap_cons, wordRows_append hm hi, wordRows_flatMap hm hi f L, List.foldl_cons,
      (foldl_mulRows (fun x => wf_wordRows hm hi (f x)) L _
        (wf_mulRows wf_idRows (wf_wordRows hm hi (f x)))).2,
      idRows_mulRows (wf_wordRows hm hi (f x))]

@[expose] def selRows (T : Nat → Array V2) (c : Nat) (L : List Nat) (acc : Array V2) : Array V2 :=
  L.foldl (fun acc j => if c.testBit j then mulRows acc (T j) else acc) acc

theorem foldl_sel {mats invs : Array (Array V2)}
    (hm : ∀ k : Nat, WfA (mats[k]?.getD (idRows ())))
    (hi : ∀ k : Nat, WfA (invs[k]?.getD (idRows ()))) (w : Nat → List Int) (c : Nat) :
    ∀ (L : List Nat) (acc : Array V2), WfA acc →
      L.foldl (fun acc j => mulRows acc (wordRows mats invs (if c.testBit j then w j else [])))
        acc = selRows (fun j => wordRows mats invs (w j)) c L acc
  | [], _, _ => rfl
  | j :: L, acc, h => by
    unfold selRows
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hb : c.testBit j
    · simp only [hb, ↓reduceIte]
      exact foldl_sel hm hi w c L _ (wf_mulRows h (wf_wordRows hm hi _))
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [show wordRows mats invs [] = idRows () from rfl, mulRows_idRows (rows_wf_of h)]
      exact foldl_sel hm hi w c L _ h

theorem bitB_eq (m j : Nat) : bitB m j = m.testBit j := by
  change Nat.beq ((m >>> j) &&& 1) 1 = _
  rw [Nat.testBit, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (m >>> j) with h | h <;> (simp [h]; try rfl)

theorem enc_selRows {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (T : Nat → Array V2) (m : Nat) :
    ∀ (P : List (Nat × Nat)), (∀ p ∈ P, WfA (T p.1) ∧ encR (T p.1) = p.2) →
      ∀ (acc : Array V2), WfA acc →
        WfA (selRows T m (P.map Prod.fst) acc) ∧
          encR (selRows T m (P.map Prod.fst) acc) = selPK c rm P m (encR acc)
  | [], _, acc, h => ⟨h, rfl⟩
  | (j, M) :: P, hP, acc, h => by
    have hjM := hP (j, M) List.mem_cons_self
    have hP' : ∀ p ∈ P, WfA (T p.1) ∧ encR (T p.1) = p.2 :=
      fun p hp => hP p (List.mem_cons_of_mem _ hp)
    unfold selRows
    rw [List.map_cons, List.foldl_cons]
    change WfA (selRows T m (P.map Prod.fst) _) ∧ encR (selRows T m (P.map Prod.fst) _) =
      Bool.rec (motive := fun _ => Nat) (selPK c rm P m (encR acc))
        (strictN (mulJ c rm (encR acc) M) (selPK c rm P m)) (bitB m j)
    rw [bitB_eq]
    by_cases hb : m.testBit j
    · simp only [hb, ↓reduceIte]
      have := enc_selRows hK T m P hP' _ (wf_mulRows h hjM.1)
      rw [enc_mulRows hK h hjM.1, hjM.2] at this
      refine ⟨this.1, ?_⟩
      rw [this.2]
      exact (strictN_eq _ _).symm
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact enc_selRows hK T m P hP' acc h

variable {one : Nat}

theorem gens_append {M1 M2 : Array (Array V2)} {l1 l2 : List Nat} (hs : M1.size = l1.length)
    (h1 : ∀ k, WfA (M1[k]?.getD (idRows ())) ∧ encR (M1[k]?.getD (idRows ())) = getN one l1 k)
    (h2 : ∀ k, WfA (M2[k]?.getD (idRows ())) ∧ encR (M2[k]?.getD (idRows ())) = getN one l2 k)
    (k : Nat) :
    WfA ((M1 ++ M2)[k]?.getD (idRows ())) ∧ encR ((M1 ++ M2)[k]?.getD (idRows ())) =
      getN one (l1 ++ l2) k := by
  rw [getN_append]
  by_cases hk : k < M1.size
  · have hk' : k < l1.length := hs ▸ hk
    rw [Array.getElem?_append_left hk]
    simp only [hk', ↓reduceIte]
    exact h1 k
  · have hk' : ¬ k < l1.length := by omega
    rw [Array.getElem?_append_right (by omega)]
    simp only [hk', ↓reduceIte, hs]
    exact h2 _

private theorem blt_bit (m j : Nat) :
    Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j)) = m.testBit j := by
  change Nat.blt 0 (m &&& 1 <<< j) = _
  have e : m &&& 1 <<< j = if m.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases e : j = i
    · subst e
      cases h : m.testBit j <;> simp [Nat.testBit_two_pow_self]
    · cases h : m.testBit j <;> simp [e, Nat.testBit_two_pow_of_ne e]
  rw [e]
  cases m.testBit j
  · rfl
  · simp only [↓reduceIte]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos j)

private theorem etaFrom_cons (c rm M : Nat) (L : List Nat) (m j acc : Nat) :
    etaFrom c rm (M :: L) m j acc = Bool.rec (motive := fun _ => Nat) (etaFrom c rm L m (j + 1) acc)
      (strictN (mulJ c rm acc M) (etaFrom c rm L m (j + 1)))
      (Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) j))) := rfl

private theorem eta_gen {c rm pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (T : Array (Array V2)) (m : Nat) :
    ∀ (L : List Nat) (j : Nat) (acc : Array V2), WfA acc →
      (∀ i < L.length, WfA (T[j + i]?.getD (idRows ())) ∧
        encR (T[j + i]?.getD (idRows ())) = getN one L i) →
      WfA ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          mulRows acc (T[j]?.getD (idRows ())) else acc) acc) ∧
        encR ((List.range' j L.length).foldl (fun acc j => if m.testBit j then
          mulRows acc (T[j]?.getD (idRows ())) else acc) acc) = etaFrom c rm L m j (encR acc)
  | [], _, acc, h, _ => ⟨h, rfl⟩
  | M :: L, j, acc, h, hT => by
    have h0 := hT 0 (by simp)
    rw [Nat.add_zero] at h0
    have hT' : ∀ i < L.length, WfA (T[j + 1 + i]?.getD (idRows ())) ∧
        encR (T[j + 1 + i]?.getD (idRows ())) = getN one L i := by
      intro i hi
      have := hT (i + 1) (by simp; omega)
      rw [show j + (i + 1) = j + 1 + i by omega] at this
      exact this
    rw [List.length_cons, List.range'_succ, List.foldl_cons, etaFrom_cons, blt_bit]
    by_cases hb : m.testBit j
    · simp only [hb, ↓reduceIte]
      have ih := eta_gen hK T m L (j + 1) _ (wf_mulRows h h0.1) hT'
      rw [enc_mulRows hK h h0.1, h0.2] at ih
      refine ⟨ih.1, ?_⟩
      rw [ih.2]
      exact (strictN_eq _ _).symm
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact eta_gen hK T m L (j + 1) acc h hT'

theorem enc_etaRows {c rm pad t0 t1 t2 t3 t4 t5 t6 : Nat}
    (_hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {T : Array (Array V2)} {Ts : List Nat}
    (_hT : ∀ j < Ts.length, WfA (T[j]?.getD (idRows ())) ∧ encR (T[j]?.getD (idRows ())) = getN one Ts j)
    (m : Nat) : WfA (etaRows T Ts.length m) ∧ encR (etaRows T Ts.length m) = etaK c rm one Ts m := by
  have h := eta_gen _hK T m Ts 0 (idRows ()) wf_idRows (fun i hi => by
    rw [Nat.zero_add]
    exact _hT i hi)
  rw [enc_idRows _hK] at h
  unfold etaRows etaK
  rw [List.range_eq_range']
  exact h

private theorem lt64' (x : UInt64) : x.toNat < 2 ^ 64 := x.toNat_lt

private theorem v2N_testBit' (v : V2) (k : Nat) :
    (v2N v).testBit k = if k < 64 then v.lo.toNat.testBit k else v.hi.toNat.testBit (k - 64) := by
  change (v.lo.toNat ||| (v.hi.toNat <<< 64)).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hk : k < 64
  · have h1 : ¬ k ≥ 64 := by omega
    simp [hk, h1]
  · have h1 : k ≥ 64 := by omega
    have h2 : v.lo.toNat.testBit k = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (lt64' v.lo) (Nat.pow_le_pow_right (by omega) h1))
    simp [hk, h1, h2]

private theorem testBit_V2' (a : V2) {j : Nat} (hj : j < 128) :
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
  rw [v2N_testBit']
  by_cases h : j < 64
  · have h0 : j / 64 = 0 := Nat.div_eq_of_lt h
    rw [ite_eq_left h0, ite_eq_left h, key, Nat.mod_eq_of_lt h]
  · have h0 : ¬ j / 64 = 0 := by omega
    have hj' : j % 64 = j - 64 := by omega
    rw [ite_eq_right h0, ite_eq_right h, key, hj']

private theorem wf_bit' {v : V2} (hv : v.wf = true) {k : Nat} (hk : 112 ≤ k) :
    (v2N v).testBit k = false := by
  have hhi : v.hi.toNat < 2 ^ 48 := by
    unfold V2.wf at hv
    rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_shiftRight, UInt64.toNat_zero] at hv
    have e : (48 : UInt64).toNat % 64 = 48 := rfl
    rw [e, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hv
    rcases hv with hv | hv
    · exact absurd hv (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 48))
    · exact hv
  rw [v2N_testBit']
  have h1 : ¬ k < 64 := by omega
  rw [ite_eq_right h1]
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by omega) (by omega)))

theorem differs_eq {a b : V2} (_ha : a.wf = true) (_hb : b.wf = true) :
    differs a b = neN (v2N a) (v2N b) := by
  have hrepr (v : V2) : v2N v = v.toNat := by
    unfold v2N V2.toNat
    rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm,
      ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt v.lo) v.hi.toNat,
      Nat.shiftLeft_eq]
    omega
  have hfalse (h : differs a b = false) : a = b := by
    apply V2.eq_of_toVec_eq _ha _hb
    unfold differs at h
    simp only [List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, not_not] at h
    funext j
    rw [V2.toVec_apply, V2.toVec_apply, h j.val j.isLt]
  by_cases he : a = b
  · subst b
    simp [differs, neN, notB]
  · have hd : differs a b = true := by
      cases h : differs a b
      · exact False.elim (he (hfalse h))
      · rfl
    have hp : v2N a ≠ v2N b := by
      intro h
      apply he
      apply V2.toNat_injective
      simpa only [hrepr] using h
    unfold neN
    rw [hd, nbeq_false hp]
    rfl

end CFSG.KC.J4Q

end
