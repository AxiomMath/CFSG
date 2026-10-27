module

public import CFSG.Certificates.Kernel.Th.S.SurjS
public import CFSG.Sporadic.Bridge.ThData
public import CFSG.Certificates.Kernel.Th.Spec.Seed
import CFSG.Certificates.Kernel.Common.StrSplit

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.SurjS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.Th

@[expose] noncomputable def hexSum : ℕ → List Char → ℕ
  | _, [] => 0
  | j, ch :: ds => hexD ch.toNat * 16 ^ j + hexSum (j + 1) ds

private theorem stStrictB (y : ℕ) (k : ℕ → Bool) : SeedS.strictB y k = k y := by cases y <;> rfl

private theorem stBeq {a b : ℕ} : Nat.beq a b = true ↔ a = b := iff_of_eq Nat.beq_eq

private theorem stBlt {a b : ℕ} : Nat.blt a b = true ↔ a < b := iff_of_eq Nat.blt_eq

private theorem stAndB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem stRun_nil {RB : ℕ → ℕ} {rm q j acc : ℕ}
    (h : textRun RB rm [] q j acc = true) : q = 1984 ∧ j = 0 := by
  have h' : andB (Nat.beq q 1984) (Nat.beq j 0) = true := h
  rw [stAndB, stBeq, stBeq] at h'
  exact h'

private theorem stRun_cons_nl {RB : ℕ → ℕ} {rm : ℕ} {ch : Char} {l : List Char} {q j acc : ℕ}
    (hb : Nat.beq ch.toNat 10 = true) :
    textRun RB rm (ch :: l) q j acc =
      andB (andB (Nat.beq j 62) (Nat.blt q 1984))
        (andB (Nat.beq (textRow RB rm q) acc) (textRun RB rm l (q + 1) 0 0)) := by
  delta textRun
  dsimp only
  simp only [stStrictB, hb]

private theorem stRun_cons_digit {RB : ℕ → ℕ} {rm : ℕ} {ch : Char} {l : List Char} {q j acc : ℕ}
    (hb : Nat.beq ch.toNat 10 = false) :
    textRun RB rm (ch :: l) q j acc =
      andB (andB (Nat.blt (hexD ch.toNat) 16) (Nat.blt j 62))
        (textRun RB rm l q (j + 1) (acc + Nat.shiftLeft (hexD ch.toNat) (Nat.mul 4 j))) := by
  delta textRun
  dsimp only
  simp only [stStrictB, hb]
  rfl

private theorem stRun_nl {RB : ℕ → ℕ} {rm : ℕ} {ch : Char} {l : List Char} {q j acc : ℕ}
    (h10 : ch.toNat = 10) (h : textRun RB rm (ch :: l) q j acc = true) :
    j = 62 ∧ q < 1984 ∧ textRow RB rm q = acc ∧ textRun RB rm l (q + 1) 0 0 = true := by
  rw [stRun_cons_nl (stBeq.2 h10), stAndB, stAndB, stAndB, stBeq, stBlt, stBeq] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

private theorem stRun_digit {RB : ℕ → ℕ} {rm : ℕ} {ch : Char} {l : List Char} {q j acc : ℕ}
    (h10 : ch.toNat ≠ 10) (h : textRun RB rm (ch :: l) q j acc = true) :
    hexD ch.toNat < 16 ∧ j < 62 ∧
      textRun RB rm l q (j + 1) (acc + hexD ch.toNat * 16 ^ j) = true := by
  have hb : Nat.beq ch.toNat 10 = false := by
    cases hh : Nat.beq ch.toNat 10
    · rfl
    · exact absurd (stBeq.1 hh) h10
  rw [stRun_cons_digit hb, stAndB, stAndB, stBlt, stBlt] at h
  have e : Nat.shiftLeft (hexD ch.toNat) (Nat.mul 4 j) = hexD ch.toNat * 16 ^ j := by
    show hexD ch.toNat <<< (4 * j) = _
    rw [Nat.shiftLeft_eq, pow_mul]
    norm_num
  rw [e] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem stLine {RB : ℕ → ℕ} {rm : ℕ} : ∀ (l : List Char) (q j acc : ℕ),
    textRun RB rm l q j acc = true →
      (l = [] ∧ q = 1984 ∧ j = 0) ∨
      ∃ (ds : List Char) (l' : List Char), l = ds ++ '\n' :: l' ∧ ds.length + j = 62 ∧
        (∀ ch ∈ ds, hexD ch.toNat < 16) ∧ acc + hexSum j ds = textRow RB rm q ∧ q < 1984 ∧
        textRun RB rm l' (q + 1) 0 0 = true := by
  intro l
  induction l with
  | nil =>
    intro q j acc h
    obtain ⟨h1, h2⟩ := stRun_nil h
    exact Or.inl ⟨rfl, h1, h2⟩
  | cons ch l ih =>
    intro q j acc h
    by_cases h10 : ch.toNat = 10
    · obtain ⟨h1, h2, h3, h4⟩ := stRun_nl h10 h
      refine Or.inr ⟨[], l, ?_, by simp [h1], by simp, by simpa [hexSum] using h3.symm, h2, h4⟩
      have : ch = '\n' := Char.ext (UInt32.toNat_inj.mp (by simpa using h10))
      simp [this]
    · obtain ⟨h1, h2, h3⟩ := stRun_digit h10 h
      rcases ih q (j + 1) _ h3 with ⟨-, -, h0⟩ | ⟨ds, l', hl, hlen, hd, hs, hq, hr⟩
      · omega
      · refine Or.inr ⟨ch :: ds, l', by simp [hl], by simp; omega, ?_, ?_, hq, hr⟩
        · intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact h1
          · exact hd c hc
        · rw [hexSum, ← hs]
          ring

private theorem stBle {a b : ℕ} : Nat.ble a b = true ↔ a ≤ b := iff_of_eq Nat.ble_eq

private theorem stAndBle {a b c d : ℕ} :
    andB (Nat.ble a b) (Nat.ble c d) = decide (a ≤ b ∧ c ≤ d) := by
  rw [Bool.eq_iff_iff, stAndB, stBle, stBle, decide_eq_true_iff]

private theorem stHexD (n : ℕ) : hexD n =
    if 48 ≤ n ∧ n ≤ 57 then n - 48 else if 97 ≤ n ∧ n ≤ 102 then n - 87 else 16 := by
  unfold hexD
  rw [stAndBle, stAndBle]
  by_cases h1 : 48 ≤ n ∧ n ≤ 57 <;> by_cases h2 : 97 ≤ n ∧ n ≤ 102 <;> simp [h1, h2]

private theorem stHexVal {ch : Char} (hd : hexD ch.toNat < 16) :
    (hexVal ch).toNat = hexD ch.toNat := by
  rw [stHexD] at hd ⊢
  unfold hexVal
  by_cases h1 : 48 ≤ ch.toNat ∧ ch.toNat ≤ 57
  · have h3 : ch.toNat < 58 := by omega
    simp [h1, h3, Nat.toUInt64]
    omega
  · by_cases h2 : 97 ≤ ch.toNat ∧ ch.toNat ≤ 102
    · have h3 : ¬ ch.toNat < 58 := by omega
      simp [h1, h2, h3, Nat.toUInt64]
      omega
    · simp [h1, h2] at hd


private theorem stHexSum_append (j : ℕ) : ∀ (a b : List Char),
    hexSum j (a ++ b) = hexSum j a + hexSum (j + a.length) b
  | [], b => by simp [hexSum]
  | ch :: a, b => by
    rw [List.cons_append, hexSum, hexSum, stHexSum_append (j + 1) a b, List.length_cons,
      show j + (a.length + 1) = j + 1 + a.length by omega]
    ring

private theorem stHexSum_shift : ∀ (ds : List Char) (j : ℕ), hexSum j ds = 16 ^ j * hexSum 0 ds
  | [], j => by simp [hexSum]
  | ch :: ds, j => by
    rw [hexSum, hexSum, stHexSum_shift ds (j + 1), stHexSum_shift ds 1, pow_succ]
    ring

private theorem stHexSum_lt : ∀ (ds : List Char), (∀ ch ∈ ds, hexD ch.toNat < 16) →
    hexSum 0 ds < 16 ^ ds.length
  | [], _ => by simp [hexSum]
  | ch :: ds, h => by
    have h1 := h ch (by simp)
    have h2 := stHexSum_lt ds (fun c hc => h c (by simp [hc]))
    have e : 16 ^ (ds.length + 1) = 16 * 16 ^ ds.length := by ring
    rw [hexSum, stHexSum_shift ds 1, List.length_cons, e]
    simp only [pow_zero, mul_one, pow_one]
    omega

private theorem stHexWord (cs : List Char) (hd : ∀ ch ∈ cs, hexD ch.toNat < 16) (start : ℕ) :
    ∀ len : ℕ, len ≤ 16 → start + len ≤ cs.length →
      (hexWord cs.toArray start len).toNat = hexSum 0 ((cs.drop start).take len) := by
  intro len
  induction len with
  | zero => intro _ _; simp [hexWord, hexSum]
  | succ len ih =>
    intro hl hs
    have ih' := ih (by omega) (by omega)
    have hlt : start + len < cs.length := by omega
    have hc : cs[start + len]?.getD '0' = cs[start + len] := by
      rw [List.getElem?_eq_getElem hlt]; rfl
    have hdc : hexD (cs[start + len]).toNat < 16 := hd _ (List.getElem_mem hlt)
    have hS : hexSum 0 ((cs.drop start).take len) < 16 ^ len := by
      have := stHexSum_lt ((cs.drop start).take len) (fun ch hch =>
        hd ch (List.mem_of_mem_drop (List.mem_of_mem_take hch)))
      have e : ((cs.drop start).take len).length = len := by
        simp only [List.length_take, List.length_drop]; omega
      rwa [e] at this
    have e1 : (cs.drop start).take (len + 1) =
        (cs.drop start).take len ++ [cs[start + len]] := by
      rw [List.take_succ, List.getElem?_drop, List.getElem?_eq_getElem hlt]
      rfl
    have e2 : ((cs.drop start).take len).length = len := by
      simp only [List.length_take, List.length_drop]; omega
    rw [e1, stHexSum_append, e2, zero_add, stHexSum_shift [cs[start + len]] len]
    simp only [hexSum, pow_zero, mul_one, add_zero]
    unfold hexWord at ih' ⊢
    simp only [List.getElem?_toArray] at ih'
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.getElem?_toArray, hc]
    rw [UInt64.toNat_or, ih', UInt64.toNat_shiftLeft, stHexVal hdc, UInt64.toNat_ofNat']
    have h4 : 4 * len % 2 ^ 64 % 64 = 4 * len := by
      rw [Nat.mod_eq_of_lt (by omega : 4 * len < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    rw [h4, Nat.shiftLeft_eq]
    have h5 : hexD cs[start + len].toNat * 2 ^ (4 * len) % 2 ^ 64 =
        hexD cs[start + len].toNat * 2 ^ (4 * len) := by
      refine Nat.mod_eq_of_lt ?_
      calc hexD cs[start + len].toNat * 2 ^ (4 * len) < 2 ^ 4 * 2 ^ (4 * len) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
        _ = 2 ^ (4 + 4 * len) := by rw [pow_add]
        _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [h5, Nat.or_comm, mul_comm (hexD cs[start + len].toNat),
      ← Nat.two_pow_add_eq_or_of_lt (by rwa [show 2 ^ (4 * len) = 16 ^ len by
        rw [pow_mul]; norm_num]) _, show 2 ^ (4 * len) = 16 ^ len by rw [pow_mul]; norm_num]
    ring


private theorem stHexSum_split (p : List Char) (a : ℕ) :
    hexSum 0 p = hexSum 0 (p.take a) + 16 ^ (min a p.length) * hexSum 0 (p.drop a) := by
  conv_lhs => rw [← List.take_append_drop a p, stHexSum_append, zero_add,
    stHexSum_shift (p.drop a) _]
  simp only [List.length_take]

private theorem stHexRow_toNat {p : List Char} (hlen : p.length = 62)
    (hd : ∀ ch ∈ p, hexD ch.toNat < 16) : (hexRow (String.ofList p)).toNat = hexSum 0 p := by
  have hcs : (String.ofList p).toList.toArray = p.toArray := by rw [String.toList_ofList]
  unfold hexRow
  simp only [hcs]
  unfold V4.toNat
  simp only []
  rw [stHexWord p hd 0 16 (by norm_num) (by omega), stHexWord p hd 16 16 (by norm_num) (by omega),
    stHexWord p hd 32 16 (by norm_num) (by omega), stHexWord p hd 48 14 (by norm_num) (by omega)]
  have e1 := stHexSum_split p 16
  have e2 := stHexSum_split (p.drop 16) 16
  have e3 := stHexSum_split (p.drop 32) 16
  have e4 : (p.drop 48).take 14 = p.drop 48 := List.take_of_length_le (by simp [hlen])
  rw [List.drop_drop] at e2 e3
  simp only [List.length_drop, hlen, List.drop_zero] at e1 e2 e3 ⊢
  rw [e4]
  norm_num at e1 e2 e3
  rw [e1, e2, e3]
  ring


private theorem stSplit : ∀ (pieces : List (List Char)), (∀ p ∈ pieces, ∀ ch ∈ p, ch ≠ '\n') →
    ((pieces.map fun p => p ++ ['\n']).flatten).splitOnP (· == '\n') = pieces ++ [[]]
  | [], _ => by simp
  | p :: ps, h => by
    have hp : ∀ c ∈ p, (c == '\n') = false := fun c hc => by
      simpa using h p (by simp) c hc
    have e : ((p :: ps).map fun p => p ++ ['\n']).flatten =
        p ++ '\n' :: ((ps.map fun p => p ++ ['\n']).flatten) := by simp
    rw [e, List.splitOnP_append_cons_of_forall_mem hp '\n' (by simp),
      stSplit ps (fun q hq => h q (by simp [hq]))]
    simp

private theorem stOfList_isEmpty (p : List Char) : (String.ofList p).isEmpty = p.isEmpty := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, String.ofList_eq_empty_iff, List.isEmpty_iff]

@[expose] def lineRows (pieces : List (List Char)) : Array V4 :=
  (pieces.map fun p => hexRow (String.ofList p)).toArray

theorem splitLines_ofList {pieces : List (List Char)} (hne : ∀ p ∈ pieces, p ≠ [])
    (hnl : ∀ p ∈ pieces, ∀ ch ∈ p, ch ≠ '\n') :
    ((String.ofList (pieces.map fun p => p ++ ['\n']).flatten).splitOn "\n").filter
      (fun l => !l.isEmpty) = pieces.map String.ofList := by
  have hn : "\n" = String.singleton '\n' := by decide
  rw [hn, CFSG.KC.Str.splitOn_ofList, List.splitOn_eq_splitOnP, stSplit pieces hnl,
    List.map_append, List.filter_append]
  have h1 : (pieces.map String.ofList).filter (fun l => !l.isEmpty) = pieces.map String.ofList :=
    List.filter_eq_self.2 fun s hs => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
      simpa [stOfList_isEmpty] using hne p hp
  have h2 : ([[]].map String.ofList).filter (fun l => !l.isEmpty) = [] := by
    simp [stOfList_isEmpty]
  rw [h1, h2, List.append_nil]

private theorem stParseMats {pieces : List (List Char)} (hne : ∀ p ∈ pieces, p ≠ [])
    (hnl : ∀ p ∈ pieces, ∀ ch ∈ p, ch ≠ '\n') :
    parseMats (String.ofList (pieces.map fun p => p ++ ['\n']).flatten) =
      (List.range (pieces.length / 248)).toArray.map fun k =>
        (lineRows pieces).extract (248 * k) (248 * k + 248) := by
  unfold parseMats
  rw [splitLines_ofList hne hnl, List.map_map]
  simp only [lineRows, List.size_toArray, List.length_map]
  rfl

private theorem stLines {RB : ℕ → ℕ} {rm : ℕ} : ∀ (n q : ℕ) (l : List Char),
    textRun RB rm l q 0 0 = true → q + n = 1984 →
    ∃ pieces : List (List Char), l = (pieces.map fun p => p ++ ['\n']).flatten ∧
      List.Forall₂ (fun p k => p.length = 62 ∧ (∀ ch ∈ p, hexD ch.toNat < 16) ∧
        hexSum 0 p = textRow RB rm k) pieces (List.range' q n) := by
  intro n
  induction n with
  | zero =>
    intro q l h hq
    rcases stLine l q 0 0 h with ⟨hl, -, -⟩ | ⟨-, -, -, -, -, -, hq', -⟩
    · exact ⟨[], by simp [hl], by simp⟩
    · omega
  | succ n ih =>
    intro q l h hq
    rcases stLine l q 0 0 h with ⟨-, h1, -⟩ | ⟨ds, l', hl, hlen, hd, hs, -, hr⟩
    · omega
    · obtain ⟨pieces, hp, hF⟩ := ih (q + 1) l' hr (by omega)
      refine ⟨ds :: pieces, by simp [hl, hp], ?_⟩
      rw [List.range'_succ]
      exact List.Forall₂.cons ⟨by omega, hd, by simpa using hs⟩ hF

private theorem stRowB_testBit (G r j : ℕ) (hj : j < 248) :
    (rowB (2 ^ 248 - 1) G r).testBit j = G.testBit (256 * r + j) := by
  change ((G >>> (r * 256)) &&& (2 ^ 248 - 1)).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    show r * 256 + j = 256 * r + j by omega]
  simp [hj]

theorem imgMats_spec {RB : ℕ → ℕ} {rm : ℕ} {LI : List Char} (hrm : rm = 2 ^ 248 - 1)
    (hI : imgText = String.ofList LI) (hT : textOK RB rm LI = true) :
    imgMats.size = 8 ∧ ∀ g < 8, WfRows (imgMats[g]?.getD (idRows ())) ∧
      rowsMatrix (imgMats[g]?.getD (idRows ())) = pkMat (RB (g + 1)) := by
  obtain ⟨pieces, hl, hF⟩ := stLines (RB := RB) (rm := rm) 1984 0 LI hT (by norm_num)
  have hF' := List.forall₂_iff_get.1 hF
  have hlen : pieces.length = 1984 := by simpa using hF'.1
  have hP : ∀ (i : ℕ) (h : i < pieces.length), pieces[i].length = 62 ∧
      (∀ ch ∈ pieces[i], hexD ch.toNat < 16) ∧ hexSum 0 pieces[i] = textRow RB rm i := by
    intro i h
    have := hF'.2 i h (by simpa [hlen] using h)
    simpa [List.getElem_range'] using this
  have hne : ∀ p ∈ pieces, p ≠ [] := by
    intro p hp h0
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have := (hP i hi).1
    simp [h0] at this
  have hnl : ∀ p ∈ pieces, ∀ ch ∈ p, ch ≠ '\n' := by
    intro p hp ch hch h10
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    have h1 := (hP i hi).2.1 ch hch
    have h2 : ch.toNat = 10 := by rw [h10]; rfl
    rw [h2, stHexD] at h1
    simp at h1
  have hmats : imgMats = (List.range 8).toArray.map fun k =>
      (lineRows pieces).extract (248 * k) (248 * k + 248) := by
    unfold imgMats
    rw [hI, hl, stParseMats hne hnl, hlen]
  rw [hmats]
  have hrsize : (lineRows pieces).size = 1984 := by simp [lineRows, hlen]
  refine ⟨by simp, fun g hg => ?_⟩
  have hget : ((List.range 8).toArray.map fun k =>
      (lineRows pieces).extract (248 * k) (248 * k + 248))[g]? =
      some ((lineRows pieces).extract (248 * g) (248 * g + 248)) := by
    rw [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hg]
    rfl
  rw [hget, Option.getD_some]
  have hsz : ((lineRows pieces).extract (248 * g) (248 * g + 248)).size = 248 := by
    rw [Array.size_extract, hrsize]; omega
  have hMget : ∀ i (hi : i < 248), ((lineRows pieces).extract (248 * g) (248 * g + 248))[i]? =
      some (hexRow (String.ofList (pieces[248 * g + i]'(by omega)))) := by
    intro i hi
    rw [Array.getElem?_extract_of_lt (by rw [hrsize]; omega)]
    simp [lineRows]
  constructor
  · refine ⟨hsz, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hx
    have hi' : i < 248 := hsz ▸ hi
    have hm := hMget i hi'
    rw [Array.getElem?_eq_getElem hi] at hm
    rw [Option.some.inj hm, V4.wf_iff_toNat_lt]
    obtain ⟨h1, h2, -⟩ := hP (248 * g + i) (by omega)
    rw [stHexRow_toNat h1 h2]
    have := stHexSum_lt _ h2
    rwa [h1, show (16 : ℕ) ^ 62 = 2 ^ 248 by norm_num] at this
  · ext i j
    have hj := j.isLt
    have hm := hMget i.val i.isLt
    rw [rowsMatrix_apply, hm, Option.getD_some, V4.toVec_apply, pkMat_apply]
    obtain ⟨h1, h2, h3⟩ := hP (248 * g + i.val) (by omega)
    have e2 : textRow RB rm (248 * g + i.val) = rowB rm (RB (g + 1)) i.val := by
      show rowB rm (RB (Nat.succ ((248 * g + i.val) / 248))) ((248 * g + i.val) % 248) = _
      have e3 : (248 * g + i.val) / 248 = g := by omega
      have e4 : (248 * g + i.val) % 248 = i.val := by omega
      rw [e3, e4]
    have e1 : (hexRow (String.ofList (pieces[248 * g + i.val]'(by omega)))).testBit j.val =
        (RB (g + 1)).testBit (256 * i.val + j.val) := by
      rw [← V4.testBit_toNat _ (by omega : j.val < 256), stHexRow_toNat h1 h2, h3, e2, hrm,
        stRowB_testBit _ _ _ hj]
    rw [e1]

end CFSG.KC.Th.Spec

end
