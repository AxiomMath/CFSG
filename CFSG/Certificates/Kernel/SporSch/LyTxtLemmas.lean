module

public import Certificates.Data.Kernel.SporSch.LySeven
public import CFSG.Sporadic.Schreier.LyCheckOrbit
import all Init.Data.String.Legacy
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Batteries.Data.String.Lemmas
import Std.Data.String.ToInt
import Std.Data.String.ToNat
import CFSG.Certificates.Kernel.SporSch.StrNl
import Std.Data.DTreeMap.Internal.Operations

public section

namespace CFSG.KS.SporSch.LyTxt

open String CFSG.KC.Enum CFSG.KS.SporSch.LyM CFSG.KS.SporSch.LySev

private theorem sp_get0 : Pos.Raw.get " " 0 = ' ' := rfl
private theorem sp_next0 : Pos.Raw.next " " 0 = ⟨1⟩ := rfl
private theorem nl_get0 : Pos.Raw.get "\n" 0 = '\n' := rfl
private theorem nl_next0 : Pos.Raw.next "\n" 0 = ⟨1⟩ := rfl

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

private theorem splitOnAux_nl (l m r : List Char) (acc : List String) :
    String.splitOnAux (String.ofList (l ++ m ++ r)) "\n" ⟨utf8Len l⟩ ⟨utf8Len l + utf8Len m⟩ 0 acc =
      acc.reverse ++ (List.splitOnPPrepend (· == '\n') r m.reverse).map String.ofList := by
  unfold String.splitOnAux
  simp only [List.append_assoc, atEnd_iff, rawEndPos_ofList, utf8Len_append, Pos.Raw.mk_le_mk,
    Nat.add_le_add_iff_left, (by omega : utf8Len m + utf8Len r ≤ utf8Len m ↔ utf8Len r = 0),
    utf8Len_eq_zero, List.reverse_cons, nl_get0, nl_next0]
  have hend : "\n".rawEndPos ≤ (⟨1⟩ : Pos.Raw) := by decide
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
    · have hc : c = '\n' := by simpa using h
      subst hc
      have hu : utf8Len l + (utf8Len m + '\n'.utf8Size) - 1 = utf8Len l + utf8Len m := by
        have : '\n'.utf8Size = 1 := rfl
        omega
      have hx := extract_of_valid l m ('\n' :: r)
      simp at hx
      simpa [Pos.Raw.unoffsetBy, hu, hx, Nat.add_assoc, List.splitOnPPrepend_cons_eq_ite] using
        splitOnAux_nl (l ++ m ++ ['\n']) [] r ((ofList m) :: acc)
    · simpa [Pos.Raw.unoffsetBy, List.splitOnPPrepend_cons_eq_ite, h, Nat.add_assoc] using
        splitOnAux_nl l (m ++ [c]) r acc

theorem splitOn_sp (cs : List Char) :
    (String.ofList cs).splitOn " " = (List.splitOnPPrepend (· == ' ') cs []).map String.ofList := by
  have h := splitOnAux_sp [] [] cs []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil] at h
  unfold String.splitOn
  have hne : (" " == "") = false := by decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact h

theorem splitOn_nl (cs : List Char) :
    (String.ofList cs).splitOn "\n" = (List.splitOnPPrepend (· == '\n') cs []).map String.ofList := by
  have h := splitOnAux_nl [] [] cs []
  simp only [List.nil_append, utf8Len_nil, Nat.add_zero, List.reverse_nil] at h
  unfold String.splitOn
  have hne : ("\n" == "") = false := by decide
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact h

theorem split_filter {p q : Char → Bool} (hpq : ∀ x, p x = true → q x = true) :
    ∀ (xs acc : List Char), (List.splitOnPPrepend p xs acc).map (List.filter q) =
      List.splitOnPPrepend p (xs.filter q) (acc.filter q)
  | [], acc => by simp [List.filter_reverse]
  | x :: xs, acc => by
    by_cases hq : q x = true
    · rw [List.filter_cons_of_pos hq]
      by_cases hp : p x = true
      · rw [List.splitOnPPrepend_cons_pos hp, List.splitOnPPrepend_cons_pos hp, List.map_cons,
          ← List.splitOnPPrepend_nil_right, ← List.splitOnPPrepend_nil_right, split_filter hpq xs [],
          List.filter_reverse, List.filter_nil]
      · have hp' : p x = false := by simpa using hp
        rw [List.splitOnPPrepend_cons_neg hp', List.splitOnPPrepend_cons_neg hp', split_filter hpq xs,
          List.filter_cons_of_pos hq]
    · have hq' : q x = false := by simpa using hq
      have hp' : p x = false := by
        cases h : p x
        · rfl
        · exact absurd (hpq x h) hq
      rw [List.filter_cons_of_neg (by simpa using hq'), List.splitOnPPrepend_cons_neg hp',
        split_filter hpq xs, List.filter_cons_of_neg (by simpa using hq')]

@[expose] def tv (p : List Char) : Option Int := (String.ofList p).toInt?

@[expose] def pI (cs : List Char) : List Int :=
  (List.splitOnP (· == ' ') (cs.filter (· != '\n'))).filterMap tv

theorem replace_ofList (p : List Char) :
    (String.ofList p).replace "\n" "" = String.ofList (p.filter (· != '\n')) := by
  apply String.toList_injective
  rw [CFSG.KS.SporSch.StrNl.replace_nl, String.toList_ofList, String.toList_ofList]

theorem parseInts_ofList (cs : List Char) :
    CFSG.Sporadic.LySchreier.Native.parseInts (String.ofList cs) = pI cs := by
  unfold CFSG.Sporadic.LySchreier.Native.parseInts pI
  rw [splitOn_sp, List.filterMap_map]
  have hf : (fun t : String => (t.replace "\n" "").toInt?) ∘ String.ofList =
      tv ∘ List.filter (· != '\n') := by
    funext p
    simp only [Function.comp_apply, tv, replace_ofList]
  rw [hf, ← List.filterMap_map]
  have hs := split_filter (p := (· == ' ')) (q := (· != '\n')) (fun x hx => by
    have : x = ' ' := by simpa using hx
    subst this
    decide) cs []
  simp only [List.splitOnPPrepend_nil_right, List.filter_nil] at hs
  rw [List.splitOnPPrepend_nil_right, hs]

theorem pI_append_nl (cs : List Char) : pI (cs ++ ['\n']) = pI cs := by
  unfold pI
  rw [List.filter_append]
  simp

theorem tv_nil : tv [] = none := by
  unfold tv
  rw [Option.eq_none_iff_forall_ne_some]
  intro a ha
  rcases (String.Slice.toInt?_eq_some_iff.1 ha) with ⟨b, hb, -⟩ | ⟨t, ht, -⟩
  · have h1 := String.Slice.isNat_of_toNat?_eq_some hb
    rw [String.isNat_toSlice, String.isNat_iff] at h1
    exact h1.1 rfl
  · have h2 := congrArg String.length ht
    have h1 : ("-" : String).length = 1 := by decide
    simp only [String.copy_toSlice, String.length_append, h1] at h2
    have h0 : (String.ofList []).length = 0 := by decide
    omega

theorem pI_nil : pI [] = [] := by
  unfold pI
  simp [tv_nil]

theorem isDigit_of {c : Char} (h : (Nat.ble 48 c.toNat && Nat.ble c.toNat 57) = true) :
    c.isDigit = true := by
  rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h
  unfold Char.isDigit
  simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, UInt32.le_iff_toNat_le]
  exact h

theorem char_of_beq {c : Char} {n : Nat} (h : Nat.beq c.toNat n = true) (hn : n < 128) :
    c = Char.ofNat n := by
  have e := Nat.eq_of_beq_eq_true h
  apply Char.ext
  apply UInt32.toNat_inj.mp
  rw [← Char.toNat, e]
  simp [Char.ofNat, Char.ofNatAux, Nat.isValidChar, hn, (by omega : n < 55296)]

theorem filter_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) :
    ds.filter (· != '_') = ds := by
  refine List.filter_eq_self.2 fun c hc => ?_
  have h := hd c hc
  have : c ≠ '_' := by
    rintro rfl
    exact absurd h (by decide)
  simpa using this

theorem toNat_digits {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    (String.ofList ds).toNat? = some (Nat.ofDigitChars 10 ds 0) := by
  have hn : (String.ofList ds).isNat = true :=
    String.isNat_of_isDigit (by simpa using hne) (by simpa using hd)
  rw [String.toNat?_eq_some_ofDigitChars hn, String.toList_ofList, filter_digits hd]

theorem tv_pos {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    tv ds = some (Nat.ofDigitChars 10 ds 0 : Int) := by
  unfold tv String.toInt?
  exact String.Slice.toInt?_eq_some_of_toNat?_eq_some
    (by rw [String.toNat?_toSlice]; exact toNat_digits hd hne)

theorem tv_neg {ds : List Char} (hd : ∀ c ∈ ds, c.isDigit = true) (hne : ds ≠ []) :
    tv ('-' :: ds) = some (-(Nat.ofDigitChars 10 ds 0 : Int)) := by
  unfold tv String.toInt?
  have hc : (String.ofList ('-' :: ds)).toSlice.copy = "-" ++ String.ofList ds := by
    rw [String.copy_toSlice]
    apply String.toList_injective
    simp
  rw [String.Slice.toInt?_eq_of_eq_minus_append hc, toNat_digits hd hne]
  rfl

theorem tokEq_eq {v : Nat} {neg : Bool} {x : Int} (h : tokEq v neg x = true) :
    x = if neg then -(v : Int) else (v : Int) := by
  cases x with
  | ofNat k =>
    cases neg
    · have e : Nat.beq k v = true := h
      rw [Nat.eq_of_beq_eq_true e]
      rfl
    · exact absurd h (by simp [tokEq])
  | negSucc k =>
    cases neg
    · exact absurd h (by simp [tokEq])
    · have e : Nat.beq (Nat.succ k) v = true := h
      rw [← Nat.eq_of_beq_eq_true e]
      rfl

theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bAnd_eqT (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eqT (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = if c = true then t else e := by
  cases c <;> rfl

theorem parseRun_cons (ch : Char) (cs : List Char) (v : Nat) (neg : Bool) (len : Nat)
    (L : List Int) (done : Bool) : parseRun (ch :: cs) v neg len L done =
    strictB (Char.toNat ch) (fun c =>
      bIf(done, false,
      bIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
        strictB (Nat.add (Nat.mul v (nat_lit 10)) (Nat.sub c (nat_lit 48))) (fun v' =>
          strictB (Nat.succ len) (fun len' => parseRun cs v' neg len' L false)),
      bIf(Nat.beq c (nat_lit 45),
        bAnd(Nat.beq len (nat_lit 0), bIf(neg, false, parseRun cs (nat_lit 0) true (nat_lit 0) L false)),
      bIf(bIf(Nat.beq c (nat_lit 32), true, Nat.beq c (nat_lit 10)),
        bAnd(Nat.blt (nat_lit 0) len, bAnd(bIf(neg, Nat.blt (nat_lit 0) v, true),
          List.rec (motive := fun _ => Bool) false
            (fun x rest _ => bAnd(tokEq v neg x,
              parseRun cs (nat_lit 0) false (nat_lit 0) rest (Nat.beq c (nat_lit 10)))) L)),
        false))))) := rfl

theorem parseRun_done : ∀ (cs : List Char) (v : Nat) (neg : Bool) (len : Nat) (L : List Int),
    parseRun cs v neg len L true = true → cs = [] ∧ L = []
  | [], v, neg, len, L, h => by
    refine ⟨rfl, ?_⟩
    cases L with
    | nil => rfl
    | cons x t => exact absurd h Bool.false_ne_true
  | ch :: cs, v, neg, len, L, h => by
    rw [parseRun_cons, strictB_eqT] at h
    exact absurd h Bool.false_ne_true

theorem ofDigitChars_snoc (ds : List Char) (c : Char) :
    Nat.ofDigitChars 10 (ds ++ [c]) 0 = Nat.ofDigitChars 10 ds 0 * 10 + (c.toNat - 48) := by
  rw [Nat.ofDigitChars_eq_foldl, Nat.ofDigitChars_eq_foldl, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.mul_comm]
  rfl

theorem ne_of_beq_false {c : Char} {n : Nat} (h : Nat.beq c.toNat n = false) (hn : n < 128) :
    c ≠ Char.ofNat n := by
  rintro rfl
  have e : (Char.ofNat n).toNat = n := by
    simp [Char.ofNat, Char.ofNatAux, Nat.isValidChar, hn, (by omega : n < 55296), Char.toNat]
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem parse_inv : ∀ (cs : List Char) (ds : List Char) (v len : Nat) (neg : Bool) (L : List Int),
    (∀ c ∈ ds, c.isDigit = true) → len = ds.length → v = Nat.ofDigitChars 10 ds 0 →
    parseRun cs v neg len L false = true →
    (List.splitOnPPrepend (· == ' ') (cs.filter (· != '\n'))
      (if neg then '-' :: ds else ds).reverse).filterMap tv = L
  | [], ds, v, len, neg, L, _, _, _, h => by
    exact absurd h Bool.false_ne_true
  | ch :: cs, ds, v, len, neg, L, hd, hl, hv, h => by
    rw [parseRun_cons, strictB_eqT] at h
    simp only [bAnd_eqT] at h
    by_cases hdig : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = true
    · simp only [hdig] at h
      rw [strictB_eqT, strictB_eqT] at h
      have hdc := isDigit_of hdig
      have hnl : (ch != '\n') = true := by
        have : ch ≠ '\n' := by
          rintro rfl
          exact absurd hdc (by decide)
        simpa using this
      have hsp : (ch == ' ') = false := by
        have : ch ≠ ' ' := by
          rintro rfl
          exact absurd hdc (by decide)
        simpa using this
      rw [List.filter_cons_of_pos (p := fun x => x != '\n') hnl,
        List.splitOnPPrepend_cons_neg (p := fun x => x == ' ') hsp]
      have := parse_inv cs (ds ++ [ch]) _ _ neg L
        (fun c hc => by
          rcases List.mem_append.1 hc with hc | hc
          · exact hd c hc
          · rw [List.mem_singleton.1 hc]
            exact hdc)
        (by rw [List.length_append, List.length_singleton, hl]) (by rw [ofDigitChars_snoc, hv]; rfl) h
      cases neg
      · simpa using this
      · simpa using this
    · have hdig' : (Nat.ble 48 ch.toNat && Nat.ble ch.toNat 57) = false := Bool.eq_false_iff.2 hdig
      simp only [hdig'] at h
      by_cases hmin : Nat.beq ch.toNat 45 = true
      · simp only [hmin, Bool.true_and, Bool.and_eq_true] at h
        obtain ⟨h0, h⟩ := h
        cases neg
        · simp only at h
          have hds : ds = [] := by
            have := Nat.eq_of_beq_eq_true h0
            rw [hl] at this
            exact List.eq_nil_of_length_eq_zero this
          subst hds
          have hc' : ch = '-' := char_of_beq hmin (by decide)
          subst hc'
          rw [List.filter_cons_of_pos (by decide), List.splitOnPPrepend_cons_neg (by decide)]
          exact parse_inv cs [] 0 0 true L (fun c hc => absurd hc List.not_mem_nil) rfl
            Nat.ofDigitChars_nil.symm h
        · exact absurd h Bool.false_ne_true
      · have hmin' : Nat.beq ch.toNat 45 = false := Bool.eq_false_iff.2 hmin
        simp only [hmin'] at h
        by_cases h32 : Nat.beq ch.toNat 32 = true
        · have hc : ch = ' ' := char_of_beq h32 (by decide)
          subst hc
          simp only [h32, Bool.true_and, Bool.and_eq_true] at h
          obtain ⟨hlen, -, h⟩ := h
          cases L with
          | nil => exact absurd h Bool.false_ne_true
          | cons x rest =>
            simp only [Bool.and_eq_true] at h
            obtain ⟨hx, h⟩ := h
            have hne : ds ≠ [] := by
              rintro rfl
              rw [hl] at hlen
              exact absurd hlen (by decide)
            have htok : tv (if neg then '-' :: ds else ds) = some x := by
              rw [tokEq_eq hx, hv]
              cases neg
              · exact tv_pos hd hne
              · exact tv_neg hd hne
            have h10 : Nat.beq (' ' : Char).toNat 10 = false := by decide
            rw [h10] at h
            rw [List.filter_cons_of_pos (by decide), List.splitOnPPrepend_cons_pos (by decide),
              List.reverse_reverse, List.filterMap_cons, htok, ← List.splitOnPPrepend_nil_right]
            have := parse_inv cs [] 0 0 false rest (fun c hc => absurd hc List.not_mem_nil) rfl
              Nat.ofDigitChars_nil.symm h
            simp only [Bool.false_eq_true, ↓reduceIte, List.reverse_nil] at this
            rw [this]
        · have h32' : Nat.beq ch.toNat 32 = false := Bool.eq_false_iff.2 h32
          simp only [h32'] at h
          by_cases h10 : Nat.beq ch.toNat 10 = true
          · have hc : ch = '\n' := char_of_beq h10 (by decide)
            subst hc
            simp only [h10, Bool.true_and, Bool.and_eq_true] at h
            obtain ⟨hlen, -, h⟩ := h
            cases L with
            | nil => exact absurd h Bool.false_ne_true
            | cons x rest =>
              simp only [Bool.and_eq_true] at h
              obtain ⟨hx, h⟩ := h
              have hne : ds ≠ [] := by
                rintro rfl
                rw [hl] at hlen
                exact absurd hlen (by decide)
              have htok : tv (if neg then '-' :: ds else ds) = some x := by
                rw [tokEq_eq hx, hv]
                cases neg
                · exact tv_pos hd hne
                · exact tv_neg hd hne
              obtain ⟨rfl, rfl⟩ := parseRun_done cs 0 false 0 rest h
              rw [List.filter_cons_of_neg (by decide), List.filter_nil, List.splitOnPPrepend_nil,
                List.reverse_reverse, List.filterMap_cons, htok, List.filterMap_nil]
          · have h10' : Nat.beq ch.toNat 10 = false := Bool.eq_false_iff.2 h10
            simp only [h10'] at h
            exact absurd h Bool.false_ne_true

theorem parseK_pI {cs : List Char} {L : List Int} (h : parseK cs L = true) : pI cs = L := by
  have := parse_inv cs [] 0 0 false L (fun c hc => absurd hc List.not_mem_nil) rfl
    Nat.ofDigitChars_nil.symm h
  simpa [pI] using this

theorem linesRun_cons (ch : Char) (cs acc : List Char) (LS : List (List Int)) :
    linesRun (ch :: cs) acc LS = bIf(Nat.beq (Char.toNat ch) (nat_lit 10),
      List.rec (motive := fun _ => Bool) false (fun L LS' _ =>
        bAnd(List.rec (motive := fun _ => Bool)
          (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
          (fun _ _ _ => CFSG.KS.SporSch.LyM.parseK (List.reverse (List.cons ch acc)) L) acc,
          linesRun cs [] LS')) LS,
      linesRun cs (List.cons ch acc) LS) := rfl

theorem lines_inv : ∀ (cs acc : List Char) (LS : List (List Int)), linesRun cs acc LS = true →
    ∀ k (hk : k < LS.length), ∃ hk' : k < (List.splitOnPPrepend (· == '\n') cs acc).length,
      pI (List.splitOnPPrepend (· == '\n') cs acc)[k] = LS[k]
  | [], acc, LS, h => by
    intro k hk
    cases LS with
    | nil => exact absurd hk (by simp)
    | cons L LS' =>
      have e : linesRun [] acc (L :: LS') = false := by
        cases acc <;> rfl
      rw [e] at h
      exact absurd h Bool.false_ne_true
  | ch :: cs, acc, LS, h => by
    intro k hk
    rw [linesRun_cons] at h
    by_cases h10 : Nat.beq ch.toNat 10 = true
    · have hc : ch = '\n' := char_of_beq h10 (by decide)
      subst hc
      simp only [h10] at h
      rw [List.splitOnPPrepend_cons_pos (by decide)]
      cases LS with
      | nil => exact absurd hk (by simp)
      | cons L LS' =>
        simp only [bAnd_eqT, Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        rcases k with _ | k
        · refine ⟨by simp, ?_⟩
          simp only [List.getElem_cons_zero]
          cases acc with
          | nil =>
            cases L with
            | nil => exact pI_nil
            | cons _ _ => exact absurd h1 Bool.false_ne_true
          | cons a acc =>
            have hp : parseK ((a :: acc).reverse ++ ['\n']) L = true := by
              have e : ((a :: acc).reverse ++ ['\n']) = List.reverse ('\n' :: a :: acc) := by simp
              rw [e]
              exact h1
            rw [← parseK_pI hp, pI_append_nl]
        · obtain ⟨hk', e⟩ := lines_inv cs [] LS' h2 k (by simpa using hk)
          simp only [List.splitOnPPrepend_nil_right] at hk' e
          exact ⟨by simpa using hk', by simpa using e⟩
    · have h10' : Nat.beq ch.toNat 10 = false := Bool.eq_false_iff.2 h10
      simp only [h10'] at h
      have hc : (ch == '\n') = false := by
        have := ne_of_beq_false h10' (by decide)
        simpa using this
      rw [List.splitOnPPrepend_cons_neg (p := fun x => x == '\n') hc]
      exact lines_inv cs (ch :: acc) LS h k hk

end CFSG.KS.SporSch.LyTxt

end
