module

public import CFSG.Certificates.Kernel.Th.S.TsS
public import CFSG.Sporadic.ThSchreier.Text
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.Th.Spec

open CFSG.Sporadic.ThSchreier

private theorem plMerge {α : Type} (p q : α → Bool) : ∀ l : List α,
    (l.splitOnP p).flatMap (fun s => s.splitOnP q) = l.splitOnP (fun c => p c || q c)
  | [] => by simp [List.splitOnP_nil]
  | c :: l => by
    have ih0 := plMerge p q l
    obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil p l)
    obtain ⟨h', t', e'⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil q h)
    have ih := ih0
    rw [e] at ih
    rw [List.splitOnP_cons_eq_ite_modifyHead,
      List.splitOnP_cons_eq_ite_modifyHead (p := fun c => p c || q c)]
    by_cases hp : p c = true
    · simp [hp, ih0]
    · by_cases hq : q c = true
      · simp [hp, hq, e, ← ih, List.splitOnP_cons_eq_ite_modifyHead]
      · simp [hp, hq, e, ← ih, List.splitOnP_cons_eq_ite_modifyHead, e']

private def plSep (c : Char) : Bool := c == '\n' || c == ' '

private def plWords (l : List Char) : List (List Char) :=
  (l.splitOnP plSep).filter fun w => !w.isEmpty

private theorem plOfList_isEmpty (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, String.ofList_eq_empty_iff, List.isEmpty_iff]

private theorem plWordsOf (l : List Char) :
    wordsOf (String.ofList l) = (plWords l).map String.ofList := by
  unfold wordsOf plWords
  have hn : "\n" = String.singleton '\n' := by decide
  have hs : " " = String.singleton ' ' := by decide
  rw [hn, CFSG.KC.Str.splitOn_ofList, List.flatMap_map]
  simp only [hs, CFSG.KC.Str.splitOn_ofList, List.splitOn_eq_splitOnP]
  rw [← List.map_flatMap]
  have hm := plMerge (fun x : Char => x == '\n') (fun x : Char => x == ' ') l
  have e : (fun c : Char => (c == '\n') || (c == ' ')) = plSep := rfl
  rw [e] at hm
  rw [hm, List.filter_map]
  congr 1
  refine List.filter_congr fun q _ => ?_
  simp only [Function.comp_apply, plOfList_isEmpty]

private theorem plWords_free {o : List Char} (ho : ∀ c ∈ o, plSep c = false) :
    plWords o = if o = [] then [] else [o] := by
  unfold plWords
  rw [List.splitOnP_eq_singleton ho]
  cases o <;> simp

private theorem plWords_sep {o : List Char} (ho : ∀ c ∈ o, plSep c = false) {sep : Char}
    (hs : plSep sep = true) (r : List Char) :
    plWords (o ++ sep :: r) = (if o = [] then [] else [o]) ++ plWords r := by
  unfold plWords
  rw [List.splitOnP_append_cons_of_forall_mem ho sep hs, List.filter_cons]
  cases o <;> simp

private theorem plSep_eq (c : Char) : TsS.isSep c.toNat = plSep c := by
  rw [Bool.eq_iff_iff]
  unfold TsS.isSep plSep
  simp only [CFSG.KC.Th.orB, Bool.or_eq_true, beq_iff_eq]
  have e32 : c.toNat = 32 ↔ c = ' ' := by
    rw [← Char.toNat_inj]
    rfl
  have e10 : c.toNat = 10 ↔ c = '\n' := by
    rw [← Char.toNat_inj]
    rfl
  have b32 : c.toNat.beq 32 = true ↔ c = ' ' := by
    rw [Nat.beq_eq]
    exact e32
  have b10 : c.toNat.beq 10 = true ↔ c = '\n' := by
    rw [Nat.beq_eq]
    exact e10
  cases h32 : c.toNat.beq 32 <;> cases h10 : c.toNat.beq 10 <;> simp_all

private theorem plAndB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

private theorem plBrecN (b : Bool) (x y : ℕ) :
    Bool.rec (motive := fun _ => ℕ) x y b = if b = true then y else x := by cases b <;> rfl

private theorem plLe (a b : Char) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]
  rfl

private theorem plDecV (n : ℕ) : TsS.decV n = if 48 ≤ n ∧ n ≤ 57 then n - 48 else 10 := by
  unfold TsS.decV
  rw [plBrecN, plAndB_eq]
  simp

private theorem plHexV (n : ℕ) : TsS.hexV n = if 48 ≤ n ∧ n ≤ 57 then n - 48 else
    if 97 ≤ n ∧ n ≤ 102 then n - 87 else if 65 ≤ n ∧ n ≤ 70 then n - 55 else 16 := by
  unfold TsS.hexV
  rw [plBrecN, plBrecN, plBrecN, plAndB_eq, plAndB_eq, plAndB_eq]
  simp

private theorem plHexV_eq {ch : Char} (h : TsS.hexV ch.toNat ≠ 16) :
    TsS.hexV ch.toNat = hexDigit ch := by
  rw [plHexV] at h ⊢
  unfold hexDigit
  simp only [plLe]
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  have ha : 'a'.toNat = 97 := rfl
  have hf : 'f'.toNat = 102 := rfl
  have hA : 'A'.toNat = 65 := rfl
  have hF : 'F'.toNat = 70 := rfl
  simp only [h0, h9, ha, hf, hA, hF]
  split_ifs at h ⊢ <;> omega

private theorem plStrictB (y : ℕ) (k : ℕ → Bool) : SeedS.strictB y k = k y := by cases y <;> rfl

section go

variable {T : ℕ → ℕ} {n : ℕ} {hex : Bool} {ch : Char} {l' : List Char} {i acc : ℕ}

private theorem plGo_nil0 : TsS.natsGo T n hex [] 0 i acc = Nat.beq i n := rfl

private theorem plGo_nil1 :
    TsS.natsGo T n hex [] 1 i acc = (Nat.beq (T i) acc && Nat.beq (i + 1) n) := by
  rw [← plAndB_eq]
  rfl

private theorem plGo_nil2 : TsS.natsGo T n hex [] 2 i acc = false := rfl

private theorem plGo_nil3 : TsS.natsGo T n hex [] 3 i acc = false := rfl

private theorem plGo_sep0 (hs : TsS.isSep ch.toNat = true) :
    TsS.natsGo T n hex (ch :: l') 0 i acc = TsS.natsGo T n hex l' 0 i acc := by
  delta TsS.natsGo
  dsimp only
  rw [plStrictB, hs]
  rfl

private theorem plGo_sep1 (hs : TsS.isSep ch.toNat = true) :
    TsS.natsGo T n hex (ch :: l') 1 i acc =
      andB (Nat.beq (T i) acc) (TsS.natsGo T n hex l' 0 (i + 1) 0) := by
  delta TsS.natsGo
  dsimp only
  rw [plStrictB, hs]
  rfl

private theorem plGo_sep2 (hs : TsS.isSep ch.toNat = true) :
    TsS.natsGo T n hex (ch :: l') 2 i acc = false := by
  delta TsS.natsGo
  dsimp only
  rw [plStrictB, hs]
  rfl

private theorem plGo_sep3 (hs : TsS.isSep ch.toNat = true) :
    TsS.natsGo T n hex (ch :: l') 3 i acc = false := by
  delta TsS.natsGo
  dsimp only
  rw [plStrictB, hs]
  rfl

private theorem plGo_dec (hs : TsS.isSep ch.toNat = false) (ph : ℕ) :
    TsS.natsGo T n false (ch :: l') ph i acc =
      Bool.rec (motive := fun _ => Bool)
        (TsS.natsGo T n false l' 1 i (10 * acc + TsS.decV ch.toNat)) false
        (Nat.beq (TsS.decV ch.toNat) 10) := by
  delta TsS.natsGo
  dsimp only
  simp only [plStrictB, hs]
  rfl

private theorem plGo_hex0 (hs : TsS.isSep ch.toNat = false) :
    TsS.natsGo T n true (ch :: l') 0 i acc =
      Bool.rec (motive := fun _ => Bool) false (TsS.natsGo T n true l' 2 i 0)
        (Nat.beq ch.toNat 48) := by
  delta TsS.natsGo
  dsimp only
  simp only [plStrictB, hs]
  rfl

private theorem plGo_hex2 (hs : TsS.isSep ch.toNat = false) :
    TsS.natsGo T n true (ch :: l') 2 i acc =
      Bool.rec (motive := fun _ => Bool) false (TsS.natsGo T n true l' 3 i 0)
        (Nat.beq ch.toNat 120) := by
  delta TsS.natsGo
  dsimp only
  simp only [plStrictB, hs]
  rfl

private theorem plGo_hexd (hs : TsS.isSep ch.toNat = false) {ph : ℕ} (hph : ph = 1 ∨ ph = 3) :
    TsS.natsGo T n true (ch :: l') ph i acc =
      Bool.rec (motive := fun _ => Bool)
        (TsS.natsGo T n true l' 1 i (16 * acc + TsS.hexV ch.toNat)) false
        (Nat.beq (TsS.hexV ch.toNat) 16) := by
  rcases hph with rfl | rfl <;>
  · delta TsS.natsGo
    dsimp only
    simp only [plStrictB, hs]
    rfl

end go

private theorem plAll_snoc {P : Char → Prop} {o : List Char} {ch : Char} (ho : ∀ c ∈ o, P c)
    (hc : P ch) : ∀ c ∈ o ++ [ch], P c := by
  intro c hc'
  rcases List.mem_append.1 hc' with h | h
  · exact ho c h
  · rw [List.mem_singleton.1 h]
    exact hc

private theorem plDecVal_snoc (o : List Char) (ch : Char) :
    CFSG.KC.Str.decVal (o ++ [ch]) = CFSG.KC.Str.decVal o * 10 + (ch.toNat - 48) := by
  simp [CFSG.KC.Str.decVal, List.foldl_append]

private theorem plDigit_of {ch : Char} (h : TsS.decV ch.toNat ≠ 10) :
    ch.isDigit = true ∧ TsS.decV ch.toNat = ch.toNat - 48 := by
  rw [plDecV] at h ⊢
  have h0 : '0'.toNat = 48 := rfl
  have h9 : '9'.toNat = 57 := rfl
  by_cases hc : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57
  · rw [if_pos hc]
    exact ⟨Char.isDigit_iff_toNat.2 ⟨by omega, by omega⟩, rfl⟩
  · rw [if_neg hc] at h
    exact absurd rfl h

private theorem plDec_run (T : ℕ → ℕ) (n : ℕ) : ∀ (l o : List Char) (ph i acc : ℕ),
    (∀ c ∈ o, plSep c = false) → (∀ c ∈ o, c.isDigit = true) → acc = CFSG.KC.Str.decVal o →
    (ph = 0 ∧ o = [] ∨ ph = 1 ∧ o ≠ []) → TsS.natsGo T n false l ph i acc = true →
    i ≤ n ∧ (plWords (o ++ l)).map (fun w => (String.ofList w).toNat!) =
      (List.range' i (n - i)).map T
  | [], o, ph, i, acc, hsf, hd, hacc, hph, h => by
    rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, hne⟩
    · rw [plGo_nil0] at h
      have hin := Nat.eq_of_beq_eq_true h
      subst hin
      refine ⟨le_rfl, ?_⟩
      simp [plWords_free (o := []) (by simp)]
    · rw [plGo_nil1] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨hT, hn⟩ := h
      have hn' : n - i = 0 + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [List.append_nil, plWords_free hsf, if_neg hne, hn']
      simp [CFSG.KC.Str.toNat!_ofList hne hd, ← hacc, hT]
  | ch :: l', o, ph, i, acc, hsf, hd, hacc, hph, h => by
    by_cases hs : TsS.isSep ch.toNat = true
    ·
      have hsep : plSep ch = true := by rw [← plSep_eq]; exact hs
      rcases hph with ⟨rfl, rfl⟩ | ⟨rfl, hne⟩
      · rw [plGo_sep0 hs] at h
        obtain ⟨hle, hmap⟩ := plDec_run T n l' [] 0 i acc (by simp) (by simp) hacc
          (Or.inl ⟨rfl, rfl⟩) h
        refine ⟨hle, ?_⟩
        rw [plWords_sep (o := []) (by simp) hsep l']
        simpa using hmap
      · rw [plGo_sep1 hs, plAndB_eq] at h
        simp only [Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨hT, h'⟩ := h
        obtain ⟨hle, hmap⟩ := plDec_run T n l' [] 0 (i + 1) 0 (by simp) (by simp) rfl
          (Or.inl ⟨rfl, rfl⟩) h'
        refine ⟨by omega, ?_⟩
        have hn' : n - i = (n - (i + 1)) + 1 := by omega
        rw [plWords_sep hsf hsep l', if_neg hne, hn', List.range'_succ]
        rw [List.nil_append] at hmap
        simp only [List.singleton_append, List.map_cons, hmap]
        rw [CFSG.KC.Str.toNat!_ofList hne hd, ← hacc, hT]
    ·
      have hs' : TsS.isSep ch.toNat = false := Bool.eq_false_iff.2 hs
      have hsep : plSep ch = false := by rw [← plSep_eq]; exact hs'
      rw [plGo_dec hs'] at h
      cases hb : Nat.beq (TsS.decV ch.toNat) 10
      · rw [hb] at h
        have hdv : TsS.decV ch.toNat ≠ 10 := Nat.ne_of_beq_eq_false hb
        obtain ⟨hdig, hval⟩ := plDigit_of hdv
        have hh : TsS.natsGo T n false l' 1 i (10 * acc + TsS.decV ch.toNat) = true := h
        obtain ⟨hle, hmap⟩ := plDec_run T n l' (o ++ [ch]) 1 i _
          (plAll_snoc hsf hsep) (plAll_snoc hd hdig)
          (by rw [plDecVal_snoc, ← hacc, hval]; omega) (Or.inr ⟨rfl, by simp⟩) hh
        refine ⟨hle, ?_⟩
        simpa using hmap
      · rw [hb] at h
        exact absurd (h : false = true) Bool.false_ne_true

private def plHexFold (ds : List Char) : ℕ := ds.foldl (fun a c => 16 * a + hexDigit c) 0

private theorem plHexFold_snoc (ds : List Char) (ch : Char) :
    plHexFold (ds ++ [ch]) = 16 * plHexFold ds + hexDigit ch := by
  simp [plHexFold, List.foldl_append]

private theorem plHexNat (ds : List Char) :
    hexNat (String.ofList ('0' :: 'x' :: ds)) = plHexFold ds := by
  simp [hexNat, plHexFold]

private theorem plHex_run (T : ℕ → ℕ) (n : ℕ) : ∀ (l o : List Char) (ph i acc : ℕ),
    (∀ c ∈ o, plSep c = false) →
    (ph = 0 ∧ o = [] ∧ acc = 0 ∨ ph = 2 ∧ o = ['0'] ∧ acc = 0 ∨
      ∃ ds, o = '0' :: 'x' :: ds ∧ acc = plHexFold ds ∧ (ph = 3 ∧ ds = [] ∨ ph = 1 ∧ ds ≠ [])) →
    TsS.natsGo T n true l ph i acc = true →
    i ≤ n ∧ (plWords (o ++ l)).map (fun w => hexNat (String.ofList w)) =
      (List.range' i (n - i)).map T
  | [], o, ph, i, acc, hsf, hph, h => by
    rcases hph with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨ds, rfl, hacc, ⟨rfl, rfl⟩ | ⟨rfl, hne⟩⟩
    · rw [plGo_nil0] at h
      have hin := Nat.eq_of_beq_eq_true h
      subst hin
      refine ⟨le_rfl, ?_⟩
      simp [plWords_free (o := []) (by simp)]
    · rw [plGo_nil2] at h
      exact absurd (h : false = true) Bool.false_ne_true
    · rw [plGo_nil3] at h
      exact absurd (h : false = true) Bool.false_ne_true
    · rw [plGo_nil1] at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      obtain ⟨hT, hn⟩ := h
      have hn' : n - i = 0 + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [List.append_nil, plWords_free hsf, if_neg (List.cons_ne_nil _ _), hn']
      simp only [List.map_cons, List.map_nil, List.range'_succ, List.range'_zero, plHexNat, ← hacc,
        hT]
  | ch :: l', o, ph, i, acc, hsf, hph, h => by
    by_cases hs : TsS.isSep ch.toNat = true
    ·
      have hsep : plSep ch = true := by rw [← plSep_eq]; exact hs
      rcases hph with ⟨rfl, rfl, hacc⟩ | ⟨rfl, rfl, hacc⟩ |
        ⟨ds, rfl, hacc, ⟨rfl, rfl⟩ | ⟨rfl, hne⟩⟩
      · rw [plGo_sep0 hs] at h
        obtain ⟨hle, hmap⟩ := plHex_run T n l' [] 0 i acc (by simp) (Or.inl ⟨rfl, rfl, hacc⟩) h
        refine ⟨hle, ?_⟩
        rw [plWords_sep (o := []) (by simp) hsep l']
        simpa using hmap
      · rw [plGo_sep2 hs] at h
        exact absurd (h : false = true) Bool.false_ne_true
      · rw [plGo_sep3 hs] at h
        exact absurd (h : false = true) Bool.false_ne_true
      · rw [plGo_sep1 hs, plAndB_eq] at h
        simp only [Bool.and_eq_true, Nat.beq_eq] at h
        obtain ⟨hT, h'⟩ := h
        obtain ⟨hle, hmap⟩ := plHex_run T n l' [] 0 (i + 1) 0 (by simp)
          (Or.inl ⟨rfl, rfl, rfl⟩) h'
        refine ⟨by omega, ?_⟩
        have hn' : n - i = (n - (i + 1)) + 1 := by omega
        rw [plWords_sep hsf hsep l', if_neg (List.cons_ne_nil _ _), hn', List.range'_succ]
        rw [List.nil_append] at hmap
        simp only [List.singleton_append, List.map_cons, hmap]
        rw [plHexNat, ← hacc, hT]
    ·
      have hs' : TsS.isSep ch.toNat = false := Bool.eq_false_iff.2 hs
      have hsep : plSep ch = false := by rw [← plSep_eq]; exact hs'
      rcases hph with ⟨rfl, rfl, hacc⟩ | ⟨rfl, rfl, hacc⟩ | ⟨ds, rfl, hacc, hph'⟩
      ·
        rw [plGo_hex0 hs'] at h
        cases hb : Nat.beq ch.toNat 48
        · rw [hb] at h
          exact absurd (h : false = true) Bool.false_ne_true
        · rw [hb] at h
          have hch : ch = '0' := Char.toNat_inj.1 (Nat.eq_of_beq_eq_true hb)
          subst hch
          obtain ⟨hle, hmap⟩ := plHex_run T n l' ['0'] 2 i 0 (plAll_snoc (o := []) (by simp) hsep)
            (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) h
          exact ⟨hle, by simpa using hmap⟩
      ·
        rw [plGo_hex2 hs'] at h
        cases hb : Nat.beq ch.toNat 120
        · rw [hb] at h
          exact absurd (h : false = true) Bool.false_ne_true
        · rw [hb] at h
          have hch : ch = 'x' := Char.toNat_inj.1 (Nat.eq_of_beq_eq_true hb)
          subst hch
          obtain ⟨hle, hmap⟩ := plHex_run T n l' ['0', 'x'] 3 i 0
            (plAll_snoc (o := ['0']) hsf hsep)
            (Or.inr (Or.inr ⟨[], rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩)) h
          exact ⟨hle, by simpa using hmap⟩
      ·
        have hph1 : ph = 1 ∨ ph = 3 := by
          rcases hph' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
        rw [plGo_hexd hs' hph1] at h
        cases hb : Nat.beq (TsS.hexV ch.toNat) 16
        · rw [hb] at h
          have hv : TsS.hexV ch.toNat ≠ 16 := Nat.ne_of_beq_eq_false hb
          have hh : TsS.natsGo T n true l' 1 i (16 * acc + TsS.hexV ch.toNat) = true := h
          obtain ⟨hle, hmap⟩ := plHex_run T n l' ('0' :: 'x' :: (ds ++ [ch])) 1 i _
            (plAll_snoc (o := '0' :: 'x' :: ds) hsf hsep)
            (Or.inr (Or.inr ⟨ds ++ [ch], rfl, by rw [plHexFold_snoc, ← hacc, plHexV_eq hv],
              Or.inr ⟨rfl, by simp⟩⟩)) hh
          exact ⟨hle, by simpa using hmap⟩
        · rw [hb] at h
          exact absurd (h : false = true) Bool.false_ne_true

theorem natsOf_ofList_of_natsRun {T : ℕ → ℕ} {n : ℕ} {l : List Char}
    (h : CFSG.KC.Th.TsS.natsRun T n false l = true) :
    CFSG.Sporadic.ThSchreier.natsOf (String.ofList l) = (List.range n).map T := by
  obtain ⟨-, hmap⟩ := plDec_run T n l [] 0 0 0 (by simp) (by simp) rfl (Or.inl ⟨rfl, rfl⟩) h
  unfold natsOf
  rw [plWordsOf, List.map_map]
  simpa [List.range_eq_range', Function.comp_def] using hmap

theorem hexsOf_ofList_of_natsRun {T : ℕ → ℕ} {n : ℕ} {l : List Char}
    (h : CFSG.KC.Th.TsS.natsRun T n true l = true) :
    CFSG.Sporadic.ThSchreier.hexsOf (String.ofList l) = (List.range n).map T := by
  obtain ⟨-, hmap⟩ := plHex_run T n l [] 0 0 0 (by simp) (Or.inl ⟨rfl, rfl, rfl⟩) h
  unfold hexsOf
  rw [plWordsOf, List.map_map]
  simpa [List.range_eq_range', Function.comp_def] using hmap

end CFSG.KC.Th.Spec

end
