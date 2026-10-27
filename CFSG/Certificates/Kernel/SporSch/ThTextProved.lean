module

public import Certificates.Data.Kernel.SporSch.ThText
public import CFSG.Sporadic.ThSchreier.Text
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.SporSch.LyTxtLemmas

namespace CFSG.KS.SporSch.ThT

open CFSG.Sporadic.ThSchreier CFSG.KC.Enum CFSG.KS.SporSch CFSG.KS.DecLines CFSG.KS.SporSch.LyTxt

def sepT (c : Char) : Bool := c == ' ' || c == '\n'

def toksT (l : List Char) : List (List Char) := (l.splitOnP sepT).filter fun p => !p.isEmpty

def hexF (o : List Char) : ℕ :=
  (if o.take 2 = ['0', 'x'] then o.drop 2 else o).foldl (fun acc c => 16 * acc + hexDigit c) 0

def accV (hex : Bool) (o : List Char) : ℕ := if hex then hexF o else Nat.ofDigitChars 10 o 0

noncomputable def dv (hex : Bool) (c : Char) : ℕ :=
  Bool.rec (motive := fun _ => Nat) (decV c.toNat) (hexV2 c.toNat) hex

def bs (hex : Bool) : ℕ := if hex then 16 else 10

def okC (hex : Bool) (c : Char) : Prop := dv hex c < bs hex

def okW (hex : Bool) (o : List Char) : Prop :=
  (∀ c ∈ o, okC hex c) ∨ (hex = true ∧ ∃ ds, o = '0' :: 'x' :: ds ∧ ∀ c ∈ ds, okC true c)

def wv (hex : Bool) (w : List Char) : ℕ :=
  if hex then hexNat (String.ofList w) else (String.ofList w).toNat!

theorem strictN_eqT' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem decV_lt {c : Char} (h : decV c.toNat < 10) :
    c.isDigit = true ∧ decV c.toNat = c.toNat - 48 := by
  unfold decV at *
  cases h1 : Nat.ble 48 c.toNat <;> cases h2 : Nat.ble c.toNat 57 <;>
    simp only [h1, h2] at h ⊢ <;> try (exact absurd h (by decide))
  exact ⟨isDigit_of (by rw [h1, h2]; rfl), rfl⟩

theorem toNat_le_iff {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]
  rfl

theorem ble_dec (a x : ℕ) : Nat.ble a x = decide (a ≤ x) := by
  cases h : Nat.ble a x
  · have : ¬ a ≤ x := fun h' => by
      rw [Nat.ble_eq_true_of_le h'] at h
      exact absurd h (by decide)
    simp [this]
  · simp [Nat.le_of_ble_eq_true h]

theorem bAnd_ble (a x b : ℕ) :
    bAnd(Nat.ble a x, Nat.ble x b) = decide (a ≤ x ∧ x ≤ b) := by
  rw [ble_dec, ble_dec]
  by_cases h1 : a ≤ x <;> by_cases h2 : x ≤ b <;> simp [h1, h2]

theorem hexV2_lt {c : Char} (h : hexV2 c.toNat < 16) : hexDigit c = hexV2 c.toNat := by
  unfold hexV2 at *
  unfold hexDigit
  simp only [toNat_le_iff]
  have e0 : ('0' : Char).toNat = 48 := rfl
  have e9 : ('9' : Char).toNat = 57 := rfl
  have ea : ('a' : Char).toNat = 97 := rfl
  have ef : ('f' : Char).toNat = 102 := rfl
  have eA : ('A' : Char).toNat = 65 := rfl
  have eF : ('F' : Char).toNat = 70 := rfl
  rw [e0, e9, ea, ef, eA, eF]
  simp only [bAnd_ble] at h ⊢
  by_cases a1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
  · simp only [a1, decide_true, and_self, ↓reduceIte]
    rfl
  · by_cases a2 : 97 ≤ c.toNat ∧ c.toNat ≤ 102
    · simp only [a1, a2, decide_true, decide_false, and_self, ↓reduceIte]
      change _ = c.toNat - 87
      omega
    · by_cases a3 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
      · simp only [a1, a2, a3, decide_true, decide_false, and_self, ↓reduceIte]
        change _ = c.toNat - 55
        omega
      · simp only [a1, a2, a3, decide_false] at h
        exact absurd h (by decide)

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  by_cases h : a = b
  · subst h
    simp [Nat.beq_refl]
  · have : Nat.beq a b = false := by
      cases e : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    simp [this, h]

theorem blt_dec (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · have : ¬ a < b := fun h' => by
      have : Nat.blt a b = true := by simpa using h'
      rw [this] at h
      exact absurd h (by decide)
    simp [this]
  · have : a < b := by simpa using h
    simp [this]

theorem rec_dec (p : Prop) [Decidable p] (x y : ℕ) :
    Bool.rec (motive := fun _ => ℕ) y x (decide p) = if p then x else y := by
  by_cases hp : p <;> simp [hp]

theorem sepT_eq (c : Char) :
    bIf(Nat.beq c.toNat 32, true, Nat.beq c.toNat 10) = sepT c := by
  have e1 : (c == ' ') = decide (c.toNat = 32) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← Char.toNat_inj]
    exact Iff.rfl
  have e2 : (c == '\n') = decide (c.toNat = 10) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← Char.toNat_inj]
    exact Iff.rfl
  rw [sepT, e1, e2, beq_dec, beq_dec]
  by_cases h1 : c.toNat = 32 <;> simp [h1]

theorem run_cons (hex : Bool) (B v : ℕ) (ch : Char) (cs : List Char) (pos acc cnt bad found : ℕ) :
    thScanRun hex B v (ch :: cs) pos acc cnt bad found =
      if sepT ch = true then
        (if pos = 0 then thScanRun hex B v cs 0 0 cnt bad found
        else thScanRun hex B v cs 0 0 (cnt + 1) (if acc < B then bad else 1)
          (if acc = v then 1 else found))
      else if hex = true ∧ ch.toNat = 120 ∧ pos = 1 ∧ acc = 0 then
        thScanRun hex B v cs 2 acc cnt bad found
      else if dv hex ch < bs hex then
        thScanRun hex B v cs (pos + 1) (bs hex * acc + dv hex ch) cnt bad found
      else thScanRun hex B v cs 1 acc cnt 1 found := by
  have e : thScanRun hex B v (ch :: cs) pos acc cnt bad found =
      strictN (Char.toNat ch) (fun c =>
        nIf(bIf(Nat.beq c 32, true, Nat.beq c 10),
          wordEnd B v pos acc cnt bad found (fun cnt bad found =>
            strictN cnt (fun cnt => thScanRun hex B v cs 0 0 cnt bad found)),
          nIf(bAnd(hex, bAnd(Nat.beq c 120, bAnd(Nat.beq pos 1, Nat.beq acc 0))),
            thScanRun hex B v cs 2 acc cnt bad found,
            strictN (Bool.rec (motive := fun _ => Nat) (decV c) (hexV2 c) hex) (fun d =>
              nIf(Nat.blt d (Bool.rec (motive := fun _ => Nat) 10 16 hex),
                strictN (Nat.add (Nat.mul (Bool.rec (motive := fun _ => Nat) 10 16 hex) acc) d)
                  (fun acc' => strictN (Nat.succ pos) (fun pos' => thScanRun hex B v cs pos' acc' cnt bad found)),
                thScanRun hex B v cs 1 acc cnt 1 found))))) := rfl
  rw [e]
  simp only [strictN_eqT', sepT_eq]
  have hb : (Bool.rec (motive := fun _ => Nat) 10 16 hex) = bs hex := by cases hex <;> rfl
  have hd : (Bool.rec (motive := fun _ => Nat) (decV ch.toNat) (hexV2 ch.toNat) hex) = dv hex ch := rfl
  rw [hb, hd]
  by_cases hs : sepT ch = true
  · rw [hs]
    simp only [↓reduceIte]
    unfold wordEnd
    rw [beq_dec, blt_dec, beq_dec]
    by_cases hp : pos = 0
    · simp [hp]
    · by_cases h1 : acc < B <;> by_cases h2 : acc = v <;> simp [hp, h1, h2, rec_dec]
  · have hs' : sepT ch = false := by simpa using hs
    rw [hs']
    simp only [Bool.false_eq_true, ↓reduceIte, beq_dec, blt_dec]
    by_cases hx : hex = true ∧ ch.toNat = 120 ∧ pos = 1 ∧ acc = 0
    · obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1
      simp [h2, h3, h4]
    · rw [ite_eq_right hx]
      have hx' : bAnd(hex, bAnd(decide (ch.toNat = 120), bAnd(decide (pos = 1), decide (acc = 0)))) =
          false := by
        cases hex
        · rfl
        · by_cases a1 : ch.toNat = 120 <;> by_cases a2 : pos = 1 <;> by_cases a3 : acc = 0 <;>
            simp_all
      rw [hx']
      by_cases hdd : dv hex ch < bs hex
      · simp [hdd]
      · simp [hdd]

theorem run_nil (hex : Bool) (B v : ℕ) (pos acc cnt bad found : ℕ) :
    thScanRun hex B v [] pos acc cnt bad found =
      if pos = 0 then 4 * cnt + (2 * found + bad)
      else 4 * (cnt + 1) + (2 * (if acc = v then 1 else found) + (if acc < B then bad else 1)) := by
  have e : thScanRun hex B v [] pos acc cnt bad found = wordEnd B v pos acc cnt bad found
      (fun cnt bad found => Nat.add (Nat.mul 4 cnt) (Nat.add (Nat.mul 2 found) bad)) := rfl
  rw [e]
  unfold wordEnd
  rw [beq_dec, blt_dec, beq_dec]
  by_cases hp : pos = 0
  · simp [hp]
  · rw [rec_dec, rec_dec]
    by_cases h1 : acc < B <;> by_cases h2 : acc = v <;> simp [hp, h1, h2]

theorem run_bad (hex : Bool) (B v : ℕ) : ∀ (cs : List Char) (pos acc cnt found : ℕ), found ≤ 1 →
    thScanRun hex B v cs pos acc cnt 1 found % 2 = 1
  | [], pos, acc, cnt, found, hf => by
    rw [run_nil]
    split_ifs <;> omega
  | ch :: cs, pos, acc, cnt, found, hf => by
    rw [run_cons]
    split_ifs <;> exact run_bad hex B v cs _ _ _ _ (by omega)

theorem okC_sep {hex : Bool} {c : Char} (h : okC hex c) : sepT c = false := by
  have e : sepT c = bIf(Nat.beq c.toNat 32, true, Nat.beq c.toNat 10) := (sepT_eq c).symm
  rw [e, beq_dec, beq_dec]
  unfold okC dv bs at h
  cases hex
  · unfold decV at h
    rw [bAnd_ble] at h
    by_cases h1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
    · have : ¬ c.toNat = 32 := by omega
      have : ¬ c.toNat = 10 := by omega
      simp [*]
    · simp [h1] at h
  · unfold hexV2 at h
    rw [bAnd_ble, bAnd_ble, bAnd_ble] at h
    by_cases h1 : c.toNat = 32
    · simp [h1] at h
    · by_cases h2 : c.toNat = 10
      · simp [h2] at h
      · simp [h1, h2]

theorem okW_sep {hex : Bool} {o : List Char} (h : okW hex o) : ∀ c ∈ o, sepT c = false := by
  rcases h with h | ⟨_, ds, rfl, hds⟩
  · exact fun c hc => okC_sep (h c hc)
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    exact okC_sep (hds c hc)

theorem toksT_single {o : List Char} (ho : ∀ c ∈ o, sepT c = false) :
    toksT o = if o = [] then [] else [o] := by
  unfold toksT
  rw [List.splitOnP_eq_singleton (p := sepT) ho]
  cases o <;> rfl

theorem toksT_sep {o : List Char} (ho : ∀ c ∈ o, sepT c = false) {s : Char} (hs : sepT s = true)
    (r : List Char) : toksT (o ++ s :: r) = (if o = [] then [] else [o]) ++ toksT r := by
  unfold toksT
  rw [List.splitOnP_append_cons_of_forall_mem (p := sepT) ho s hs r]
  cases o <;> rfl

theorem flatMap_splitT : ∀ xs : List Char,
    (xs.splitOnP (· == '\n')).flatMap (·.splitOnP (· == ' ')) = xs.splitOnP sepT
  | [] => by simp [List.splitOnP_nil]
  | x :: xs => by
    rw [List.splitOnP_cons_eq_ite_modifyHead, List.splitOnP_cons_eq_ite_modifyHead]
    by_cases hn : (x == '\n') = true
    · have hs : sepT x = true := by simp [sepT, hn]
      rw [ite_eq_left hn, ite_eq_left hs, List.flatMap_cons, flatMap_splitT xs, List.splitOnP_nil]
      rfl
    · obtain ⟨h, t, e⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == '\n') xs)
      have ih := flatMap_splitT xs
      rw [e, List.flatMap_cons] at ih
      rw [ite_eq_right hn, e, List.modifyHead_cons, List.flatMap_cons,
        List.splitOnP_cons_eq_ite_modifyHead]
      by_cases hs : (x == ' ') = true
      · have hs' : sepT x = true := by simp [sepT, hs]
        rw [ite_eq_left hs, ite_eq_left hs', ← ih]
        rfl
      · have hs' : ¬ sepT x = true := by simp_all [sepT]
        rw [ite_eq_right hs, ite_eq_right hs', ← ih]
        obtain ⟨a, b, e2⟩ := List.exists_cons_of_ne_nil (List.splitOnP_ne_nil (· == ' ') h)
        rw [e2, List.cons_append, List.modifyHead_cons, List.modifyHead_cons, List.cons_append]

theorem wordsOf_ofList (cs : List Char) :
    wordsOf (String.ofList cs) = (toksT cs).map String.ofList := by
  unfold wordsOf toksT
  rw [splitOn_nl, List.splitOnPPrepend_nil_right, List.flatMap_map]
  simp only [splitOn_sp, List.splitOnPPrepend_nil_right]
  rw [← List.map_flatMap, flatMap_splitT, List.filter_map]
  congr 1
  exact List.filter_congr fun q _ => by simp only [Function.comp_apply, ofList_isEmpty]

theorem okC_ne_x {hex : Bool} {c : Char} (h : okC hex c) : c ≠ 'x' := by
  rintro rfl
  unfold okC dv bs at h
  cases hex <;> exact absurd h (by decide)

theorem not_mem_x {hex : Bool} {o : List Char} (h : ∀ c ∈ o, okC hex c) : 'x' ∉ o :=
  fun hx => okC_ne_x (h 'x' hx) rfl

theorem hexF_plain {o : List Char} (h : 'x' ∉ o) :
    hexF o = o.foldl (fun acc c => 16 * acc + hexDigit c) 0 := by
  unfold hexF
  have : ¬ o.take 2 = ['0', 'x'] := by
    intro he
    have : 'x' ∈ o.take 2 := by rw [he]; simp
    exact h (List.mem_of_mem_take this)
  rw [ite_eq_right this]

theorem accV_nil (hex : Bool) : accV hex [] = 0 := by
  cases hex <;> simp [accV, hexF]

theorem accV_snoc {hex : Bool} {o : List Char} {ch : Char} (ho : okW hex o) (hc : okC hex ch) :
    accV hex (o ++ [ch]) = bs hex * accV hex o + dv hex ch := by
  cases hex
  · have hd := decV_lt hc
    simp only [accV, Bool.false_eq_true, ↓reduceIte, bs]
    rw [ofDigitChars_snoc, Nat.mul_comm]
    have e : dv false ch = decV ch.toNat := rfl
    rw [e, hd.2]
  · have hd : hexDigit ch = dv true ch := hexV2_lt hc
    simp only [accV, ↓reduceIte, bs]
    rcases ho with ho | ⟨_, ds, rfl, hds⟩
    · have hx : 'x' ∉ o := not_mem_x ho
      have hx' : 'x' ∉ o ++ [ch] := by
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hx, fun h => okC_ne_x hc h.symm⟩
      rw [hexF_plain hx, hexF_plain hx', List.foldl_append, List.foldl_cons, List.foldl_nil, hd]
    · simp only [hexF, List.cons_append, List.take_succ_cons, List.take_zero, ↓reduceIte,
        List.drop_succ_cons, List.drop_zero]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hd]

theorem zero_word {o : List Char} (ho : okW true o) (hl : o.length = 1) (ha : accV true o = 0) :
    o = ['0'] := by
  rcases ho with ho | ⟨_, ds, rfl, _⟩
  · obtain ⟨c, rfl⟩ : ∃ c, o = [c] := List.length_eq_one_iff.1 hl
    have hc := ho c (by simp)
    have hx : 'x' ∉ [c] := not_mem_x ho
    simp only [accV, ↓reduceIte] at ha
    rw [hexF_plain hx] at ha
    simp only [List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.zero_add] at ha
    rw [hexV2_lt hc] at ha
    unfold okC dv bs at hc
    simp only [↓reduceIte] at hc
    unfold hexV2 at ha hc
    rw [bAnd_ble, bAnd_ble, bAnd_ble] at ha hc
    have h48 : c.toNat = 48 := by
      by_cases a1 : 48 ≤ c.toNat ∧ c.toNat ≤ 57
      · simp only [a1] at ha
        change c.toNat - 48 = 0 at ha
        omega
      · by_cases a2 : 97 ≤ c.toNat ∧ c.toNat ≤ 102
        · simp only [a1, a2, decide_false] at ha
          change c.toNat - 87 = 0 at ha
          omega
        · by_cases a3 : 65 ≤ c.toNat ∧ c.toNat ≤ 70
          · simp only [a1, a2, a3, decide_false] at ha
            change c.toNat - 55 = 0 at ha
            omega
          · simp only [a1, a2, a3, decide_false] at hc
            exact absurd hc (by decide)
    have : c = '0' := Char.toNat_inj.1 h48
    rw [this]
  · simp at hl

theorem run_spec (hex : Bool) (B v : ℕ) : ∀ (cs o : List Char) (cnt bad found : ℕ), okW hex o →
    bad ≤ 1 → found ≤ 1 →
    thScanRun hex B v cs o.length (accV hex o) cnt bad found % 2 = 0 →
    bad = 0 ∧ thScanRun hex B v cs o.length (accV hex o) cnt bad found / 4 =
        cnt + (toksT (o ++ cs)).length ∧
      (∀ w ∈ toksT (o ++ cs), okW hex w ∧ accV hex w < B) ∧
      (thScanRun hex B v cs o.length (accV hex o) cnt bad found / 2 % 2 = 1 ↔
        (found = 1 ∨ ∃ w ∈ toksT (o ++ cs), accV hex w = v))
  | [], o, cnt, bad, found, ho, hb, hf, h => by
    rw [List.append_nil, toksT_single (okW_sep ho)]
    rw [run_nil] at h ⊢
    by_cases ho0 : o = []
    · subst ho0
      simp only [List.length_nil, ↓reduceIte] at h ⊢
      have hb0 : bad = 0 := by omega
      subst hb0
      have e4 : (4 * cnt + (2 * found + 0)) / 4 = cnt := by omega
      have e2 : (4 * cnt + (2 * found + 0)) / 2 % 2 = found := by omega
      rw [e4, e2]
      simp
    · have hl : o.length ≠ 0 := by simpa using ho0
      simp only [hl, ↓reduceIte, ho0] at h ⊢
      have hB : accV hex o < B := by
        by_contra hc
        simp only [hc, ↓reduceIte] at h
        omega
      simp only [hB, ↓reduceIte] at h ⊢
      have hb0 : bad = 0 := by omega
      subst hb0
      by_cases h2 : accV hex o = v
      · simp only [h2, ↓reduceIte] at h ⊢
        have e4 : (4 * (cnt + 1) + (2 * 1 + 0)) / 4 = cnt + 1 := by omega
        have e2 : (4 * (cnt + 1) + (2 * 1 + 0)) / 2 % 2 = 1 := by omega
        rw [e4, e2]
        refine ⟨trivial, by simp, ?_, ?_⟩
        · intro w hw
          rw [List.mem_singleton.1 hw]
          exact ⟨ho, hB⟩
        · simp [h2]
      · simp only [h2, ↓reduceIte] at h ⊢
        have e4 : (4 * (cnt + 1) + (2 * found + 0)) / 4 = cnt + 1 := by omega
        have e2 : (4 * (cnt + 1) + (2 * found + 0)) / 2 % 2 = found := by omega
        rw [e4, e2]
        refine ⟨trivial, by simp, ?_, ?_⟩
        · intro w hw
          rw [List.mem_singleton.1 hw]
          exact ⟨ho, hB⟩
        · simp [h2]
  | ch :: cs, o, cnt, bad, found, ho, hb, hf, h => by
    rw [run_cons] at h ⊢
    by_cases hs : sepT ch = true
    · rw [toksT_sep (okW_sep ho) hs]
      simp only [hs, ↓reduceIte] at h ⊢
      have hok0 : okW hex [] := Or.inl (by simp)
      by_cases ho0 : o = []
      · subst ho0
        simp only [List.length_nil, ↓reduceIte, List.nil_append] at h ⊢
        have ih := run_spec hex B v cs [] cnt bad found hok0 hb hf
        simp only [List.length_nil, accV_nil, List.nil_append] at ih
        exact ih h
      · have hl : o.length ≠ 0 := by simpa using ho0
        simp only [hl, ↓reduceIte, ho0, List.singleton_append] at h ⊢
        have ih := run_spec hex B v cs [] (cnt + 1) (if accV hex o < B then bad else 1)
          (if accV hex o = v then 1 else found) hok0 (by split_ifs <;> omega)
          (by split_ifs <;> omega)
        simp only [List.length_nil, accV_nil, List.nil_append] at ih
        obtain ⟨i1, i2, i3, i4⟩ := ih h
        have hB : accV hex o < B := by
          by_contra hc
          simp [hc] at i1
        simp only [hB, ↓reduceIte] at i1
        refine ⟨i1, by rw [i2, List.length_cons]; omega, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨ho, hB⟩
          · exact i3 w hw
        · rw [i4]
          by_cases h2 : accV hex o = v
          · simp [h2]
          · simp [h2]
    · have hs' : sepT ch = false := by simpa using hs
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hx : hex = true ∧ ch.toNat = 120 ∧ o.length = 1 ∧ accV hex o = 0
      · simp only [hx] at h ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        have hch : ch = 'x' := Char.toNat_inj.1 h2
        subst hch
        have hz := zero_word ho h3 h4
        subst hz
        have hok : okW true ['0', 'x'] := Or.inr ⟨rfl, [], rfl, by simp⟩
        have hl2 : (['0', 'x'] : List Char).length = 2 := rfl
        have ha2 : accV true ['0', 'x'] = 0 := by simp [accV, hexF]
        have ih := run_spec true B v cs ['0', 'x'] cnt bad found hok hb hf
        rw [hl2, ha2] at ih
        rw [h4] at h ⊢
        have e : ['0'] ++ 'x' :: cs = ['0', 'x'] ++ cs := rfl
        rw [e]
        exact ih h
      · simp only [hx, ↓reduceIte] at h ⊢
        by_cases hd : dv hex ch < bs hex
        · simp only [hd, ↓reduceIte] at h ⊢
          have hc : okC hex ch := hd
          have hok : okW hex (o ++ [ch]) := by
            rcases ho with ho | ⟨hh, ds, rfl, hds⟩
            · left
              intro c hc'
              rcases List.mem_append.1 hc' with hc' | hc'
              · exact ho c hc'
              · rw [List.mem_singleton.1 hc']
                exact hc
            · right
              refine ⟨hh, ds ++ [ch], by simp, fun c hc' => ?_⟩
              rcases List.mem_append.1 hc' with hc' | hc'
              · exact hds c hc'
              · rw [List.mem_singleton.1 hc']
                subst hh
                exact hc
          have ih := run_spec hex B v cs (o ++ [ch]) cnt bad found hok hb hf
          rw [List.length_append, List.length_singleton, accV_snoc ho hc] at ih
          have e : o ++ ch :: cs = (o ++ [ch]) ++ cs := by simp
          rw [e]
          exact ih h
        · simp only [hd, ↓reduceIte] at h
          have := run_bad hex B v cs 1 (accV hex o) cnt found hf
          omega

theorem wv_eq {hex : Bool} {w : List Char} (hw : okW hex w) (hne : w ≠ []) :
    (if hex then hexNat (String.ofList w) else (String.ofList w).toNat!) = accV hex w := by
  cases hex
  · have hd : ∀ c ∈ w, c.isDigit = true := by
      rcases hw with hw | ⟨h, _⟩
      · exact fun c hc => (decV_lt (hw c hc)).1
      · exact absurd h (by decide)
    simp only [Bool.false_eq_true, ↓reduceIte, accV]
    exact toNat!_of (toNat_digits hd hne)
  · simp only [↓reduceIte, accV, hexNat, hexF, String.toList_ofList]

theorem bind_cons (hex : Bool) (R : ℕ → ℕ) (ch : Char) (cs : List Char) (pos acc cnt bad : ℕ) :
    thBindRun hex R (ch :: cs) pos acc cnt bad =
      if sepT ch = true then
        (if pos = 0 then thBindRun hex R cs 0 0 cnt bad
        else thBindRun hex R cs 0 0 (cnt + 1) (if acc = R cnt then bad else 1))
      else if hex = true ∧ ch.toNat = 120 ∧ pos = 1 ∧ acc = 0 then
        thBindRun hex R cs 2 acc cnt bad
      else if dv hex ch < bs hex then
        thBindRun hex R cs (pos + 1) (bs hex * acc + dv hex ch) cnt bad
      else thBindRun hex R cs 1 acc cnt 1 := by
  have e : thBindRun hex R (ch :: cs) pos acc cnt bad =
      strictN (Char.toNat ch) (fun c =>
        nIf(bIf(Nat.beq c 32, true, Nat.beq c 10),
          nIf(Nat.beq pos 0, thBindRun hex R cs 0 0 cnt bad,
            strictN (Nat.succ cnt) (fun cnt' =>
              thBindRun hex R cs 0 0 cnt' (nIf(Nat.beq acc (R cnt), bad, 1)))),
          nIf(bAnd(hex, bAnd(Nat.beq c 120, bAnd(Nat.beq pos 1, Nat.beq acc 0))),
            thBindRun hex R cs 2 acc cnt bad,
            strictN (Bool.rec (motive := fun _ => Nat) (decV c) (hexV2 c) hex) (fun d =>
              nIf(Nat.blt d (Bool.rec (motive := fun _ => Nat) 10 16 hex),
                strictN (Nat.add (Nat.mul (Bool.rec (motive := fun _ => Nat) 10 16 hex) acc) d)
                  (fun acc' => strictN (Nat.succ pos) (fun pos' => thBindRun hex R cs pos' acc' cnt bad)),
                thBindRun hex R cs 1 acc cnt 1))))) := rfl
  rw [e]
  simp only [strictN_eqT', sepT_eq]
  have hb : (Bool.rec (motive := fun _ => Nat) 10 16 hex) = bs hex := by cases hex <;> rfl
  have hd : (Bool.rec (motive := fun _ => Nat) (decV ch.toNat) (hexV2 ch.toNat) hex) = dv hex ch := rfl
  rw [hb, hd]
  by_cases hs : sepT ch = true
  · rw [hs]
    simp only [↓reduceIte]
    rw [beq_dec, beq_dec]
    by_cases hp : pos = 0
    · simp [hp]
    · rw [rec_dec]
      by_cases h2 : acc = R cnt <;> simp [hp, h2]
  · have hs' : sepT ch = false := by simpa using hs
    rw [hs']
    simp only [Bool.false_eq_true, ↓reduceIte, beq_dec, blt_dec]
    by_cases hx : hex = true ∧ ch.toNat = 120 ∧ pos = 1 ∧ acc = 0
    · obtain ⟨h1, h2, h3, h4⟩ := hx
      subst h1
      simp [h2, h3, h4]
    · rw [ite_eq_right hx]
      have hx' : bAnd(hex, bAnd(decide (ch.toNat = 120), bAnd(decide (pos = 1), decide (acc = 0)))) =
          false := by
        cases hex
        · rfl
        · by_cases a1 : ch.toNat = 120 <;> by_cases a2 : pos = 1 <;> by_cases a3 : acc = 0 <;>
            simp_all
      rw [hx']
      by_cases hdd : dv hex ch < bs hex
      · simp [hdd]
      · simp [hdd]

theorem bind_nil (hex : Bool) (R : ℕ → ℕ) (pos acc cnt bad : ℕ) :
    thBindRun hex R [] pos acc cnt bad =
      if pos = 0 then 2 * cnt + bad else 2 * (cnt + 1) + (if acc = R cnt then bad else 1) := by
  have e : thBindRun hex R [] pos acc cnt bad =
      nIf(Nat.beq pos 0, Nat.add (Nat.mul 2 cnt) bad,
        Nat.add (Nat.mul 2 (Nat.succ cnt)) (nIf(Nat.beq acc (R cnt), bad, 1))) := rfl
  rw [e, beq_dec, beq_dec]
  by_cases hp : pos = 0
  · simp [hp]
  · rw [rec_dec]
    by_cases h2 : acc = R cnt <;> simp [hp, h2]

theorem bind_bad (hex : Bool) (R : ℕ → ℕ) : ∀ (cs : List Char) (pos acc cnt : ℕ),
    thBindRun hex R cs pos acc cnt 1 % 2 = 1
  | [], pos, acc, cnt => by
    rw [bind_nil]
    split_ifs <;> omega
  | ch :: cs, pos, acc, cnt => by
    rw [bind_cons]
    split_ifs <;> exact bind_bad hex R cs _ _ _

theorem bind_spec (hex : Bool) (R : ℕ → ℕ) : ∀ (cs o : List Char) (cnt bad : ℕ), okW hex o →
    bad ≤ 1 → thBindRun hex R cs o.length (accV hex o) cnt bad % 2 = 0 →
    bad = 0 ∧ thBindRun hex R cs o.length (accV hex o) cnt bad / 2 =
        cnt + (toksT (o ++ cs)).length ∧
      (∀ w ∈ toksT (o ++ cs), okW hex w) ∧
      ∀ t < (toksT (o ++ cs)).length, accV hex ((toksT (o ++ cs)).getD t []) = R (cnt + t)
  | [], o, cnt, bad, ho, hb, h => by
    rw [List.append_nil, toksT_single (okW_sep ho)]
    rw [bind_nil] at h ⊢
    by_cases ho0 : o = []
    · subst ho0
      simp only [List.length_nil, ↓reduceIte] at h ⊢
      have hb0 : bad = 0 := by omega
      subst hb0
      refine ⟨rfl, by omega, by simp, by simp⟩
    · have hl : o.length ≠ 0 := by simpa using ho0
      simp only [hl, ↓reduceIte, ho0] at h ⊢
      have hR : accV hex o = R cnt := by
        by_contra hc
        simp only [hc, ↓reduceIte] at h
        omega
      simp only [hR, ↓reduceIte] at h ⊢
      have hb0 : bad = 0 := by omega
      subst hb0
      refine ⟨rfl, by simp, by simpa using ho, fun t ht => ?_⟩
      have ht0 : t = 0 := by simpa using ht
      subst ht0
      simpa using hR
  | ch :: cs, o, cnt, bad, ho, hb, h => by
    rw [bind_cons] at h ⊢
    by_cases hs : sepT ch = true
    · rw [toksT_sep (okW_sep ho) hs]
      simp only [hs, ↓reduceIte] at h ⊢
      have hok0 : okW hex [] := Or.inl (by simp)
      by_cases ho0 : o = []
      · subst ho0
        simp only [List.length_nil, ↓reduceIte, List.nil_append] at h ⊢
        have ih := bind_spec hex R cs [] cnt bad hok0 hb
        simp only [List.length_nil, accV_nil, List.nil_append] at ih
        exact ih h
      · have hl : o.length ≠ 0 := by simpa using ho0
        simp only [hl, ↓reduceIte, ho0, List.singleton_append] at h ⊢
        have ih := bind_spec hex R cs [] (cnt + 1) (if accV hex o = R cnt then bad else 1) hok0
          (by split_ifs <;> omega)
        simp only [List.length_nil, accV_nil, List.nil_append] at ih
        obtain ⟨i1, i2, i3, i4⟩ := ih h
        have hR : accV hex o = R cnt := by
          by_contra hc
          simp [hc] at i1
        simp only [hR, ↓reduceIte] at i1
        refine ⟨i1, by rw [i2, List.length_cons]; omega, ?_, ?_⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ho
          · exact i3 w hw
        · intro t ht
          cases t with
          | zero => simpa using hR
          | succ t =>
            have := i4 t (by simpa using ht)
            simp only [List.getD_cons_succ]
            rw [this]
            congr 1
            omega
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hx : hex = true ∧ ch.toNat = 120 ∧ o.length = 1 ∧ accV hex o = 0
      · simp only [hx] at h ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        have hch : ch = 'x' := Char.toNat_inj.1 h2
        subst hch
        have hz := zero_word ho h3 h4
        subst hz
        have hok : okW true ['0', 'x'] := Or.inr ⟨rfl, [], rfl, by simp⟩
        have hl2 : (['0', 'x'] : List Char).length = 2 := rfl
        have ha2 : accV true ['0', 'x'] = 0 := by simp [accV, hexF]
        have ih := bind_spec true R cs ['0', 'x'] cnt bad hok hb
        rw [hl2, ha2] at ih
        rw [h4] at h ⊢
        have e : ['0'] ++ 'x' :: cs = ['0', 'x'] ++ cs := rfl
        rw [e]
        exact ih h
      · simp only [hx, ↓reduceIte] at h ⊢
        by_cases hd : dv hex ch < bs hex
        · simp only [hd, ↓reduceIte] at h ⊢
          have hc : okC hex ch := hd
          have hok : okW hex (o ++ [ch]) := by
            rcases ho with ho | ⟨hh, ds, rfl, hds⟩
            · left
              intro c hc'
              rcases List.mem_append.1 hc' with hc' | hc'
              · exact ho c hc'
              · rw [List.mem_singleton.1 hc']
                exact hc
            · right
              refine ⟨hh, ds ++ [ch], by simp, fun c hc' => ?_⟩
              rcases List.mem_append.1 hc' with hc' | hc'
              · exact hds c hc'
              · rw [List.mem_singleton.1 hc']
                subst hh
                exact hc
          have ih := bind_spec hex R cs (o ++ [ch]) cnt bad hok hb
          rw [List.length_append, List.length_singleton, accV_snoc ho hc] at ih
          have e : o ++ ch :: cs = (o ++ [ch]) ++ cs := by simp
          rw [e]
          exact ih h
        · simp only [hd, ↓reduceIte] at h
          have := bind_bad hex R cs 1 (accV hex o) cnt
          omega

end CFSG.KS.SporSch.ThT

namespace CFSG.KS.SporSch

open CFSG.Sporadic.ThSchreier CFSG.KS.SporSch.ThT

public theorem thScan_sound_proved {hex : Bool} {B v : Nat} {cs : List Char}
    (h : thScanK hex B v cs % 2 = 0) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = thScanK hex B v cs / 4 ∧ (∀ n ∈ L, n < B) ∧
      (v ∈ L ↔ thScanK hex B v cs / 2 % 2 = 1) := by
  have hk : thScanK hex B v cs = thScanRun hex B v cs ([] : List Char).length (accV hex []) 0 0 0 := by
    rw [accV_nil]
    rfl
  rw [hk] at h ⊢
  obtain ⟨_, h2, h3, h4⟩ := run_spec hex B v cs [] 0 0 0 (Or.inl (by simp)) (by omega) (by omega) h
  simp only [List.nil_append, Nat.zero_add] at h2 h3 h4
  have hL : (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)) =
      (toksT cs).map (accV hex) := by
    have e : (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)) =
        (wordsOf (String.ofList cs)).map
          (fun s => if hex then hexNat s else s.toNat!) := by
      cases hex <;> rfl
    rw [e, wordsOf_ofList, List.map_map]
    refine List.map_congr_left fun w hw => ?_
    have hne : w ≠ [] := by
      have := (List.mem_filter.1 hw).2
      simpa using this
    exact wv_eq (h3 w hw).1 hne
  intro L
  change (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)).length = _ ∧
    (∀ n ∈ (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)), n < B) ∧
    (v ∈ (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)) ↔ _)
  rw [hL, List.length_map, h2, h4]
  refine ⟨rfl, fun n hn => ?_, ?_⟩
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hn
    exact (h3 w hw).2
  · simp only [List.mem_map]
    constructor
    · rintro ⟨w, hw, hv⟩
      exact Or.inr ⟨w, hw, hv⟩
    · rintro (h0 | ⟨w, hw, hv⟩)
      · exact absurd h0 (by decide)
      · exact ⟨w, hw, hv⟩

public theorem thBind_sound_proved {hex : Bool} {R : Nat → Nat} {cs : List Char}
    (h : thBindK hex R cs % 2 = 0) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = thBindK hex R cs / 2 ∧ ∀ t < L.length, L.getD t 0 = R t := by
  have hk : thBindK hex R cs = thBindRun hex R cs ([] : List Char).length (accV hex []) 0 0 := by
    rw [accV_nil]
    rfl
  rw [hk] at h ⊢
  obtain ⟨_, h2, h3, h4⟩ := bind_spec hex R cs [] 0 0 (Or.inl (by simp)) (by omega) h
  simp only [List.nil_append, Nat.zero_add] at h2 h3 h4
  have hL : (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)) =
      (toksT cs).map (accV hex) := by
    have e : (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)) =
        (wordsOf (String.ofList cs)).map
          (fun s => if hex then hexNat s else s.toNat!) := by
      cases hex <;> rfl
    rw [e, wordsOf_ofList, List.map_map]
    refine List.map_congr_left fun w hw => ?_
    have hne : w ≠ [] := by
      have := (List.mem_filter.1 hw).2
      simpa using this
    exact wv_eq (h3 w hw) hne
  intro L
  change (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)).length = _ ∧
    ∀ t < (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)).length,
      (if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)).getD t 0 = R t
  rw [hL, List.length_map, h2]
  refine ⟨rfl, fun t ht => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ht,
    Option.map_some, Option.getD_some, ← h4 t ht, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht, Option.getD_some]

end CFSG.KS.SporSch
