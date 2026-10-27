module

public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv
public import CFSG.Certificates.Kernel.Spor.PK.BFS

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] def letFn (gens : Int → Nat → Nat) (L : List (Nat → Nat)) (z : Int) : Nat → Nat :=
  if z.natAbs ≤ 2 then gens z
  else if 0 < z then L.getD (2 * (z.natAbs - 3)) id else L.getD (2 * (z.natAbs - 3) + 1) id

@[expose] def wordFn (gens : Int → Nat → Nat) (L : List (Nat → Nat)) (wd : List Int) (x : Nat) :
    Nat :=
  wd.foldr (fun z y => letFn gens L z y) x

@[expose] def lettersFrom (n : Nat) (gens : Int → Nat → Nat) (L : List (Nat → Nat))
    (ws : List (List Int)) : List (Nat → Nat) :=
  ws.foldl (fun L wd => L ++ [wordFn gens L wd, finv n (wordFn gens L wd)]) L

@[expose] def lettersFn (n : Nat) (gens : Int → Nat → Nat) (ws : List (List Int)) :
    List (Nat → Nat) :=
  lettersFrom n gens [] ws

theorem icode_eq (z : Int) : icode z = if 0 ≤ z then 2 * z.natAbs else 2 * z.natAbs + 1 := by
  cases z with
  | ofNat k =>
    have h : (0 : Int) ≤ Int.ofNat k := Int.ofNat_nonneg k
    show k + k = _
    rw [if_pos h]
    simp only [Int.natAbs_ofNat']
    omega
  | negSucc k =>
    show k + 1 + (k + 1) + 1 = _
    rw [if_neg (Int.not_le.2 (Int.negSucc_lt_zero k))]
    simp only [Int.natAbs_negSucc]
    omega

private theorem icode_shiftRight (z : Int) : Nat.shiftRight (icode z) 1 = z.natAbs := by
  show icode z >>> 1 = _
  rw [icode_eq]
  split <;> omega

private theorem icode_pos (z : Int) : 0 < icode z ↔ z ≠ 0 := by
  rw [icode_eq]
  split <;> omega

private theorem icode_land_one (z : Int) : Nat.land (icode z) 1 = if 0 ≤ z then 0 else 1 := by
  show icode z &&& 1 = _
  rw [Nat.and_one_is_mod, icode_eq]
  split <;> omega

private noncomputable def chkZ (j : Nat) (z : Int) (ih : Bool) : Bool :=
  strictB (icode z) (fun c => strictB (Nat.shiftRight c (nat_lit 1)) (fun a =>
    bAnd(Nat.blt (nat_lit 0) c,
    bAnd(bIf(Nat.ble a (nat_lit 2), true, Nat.blt a (Nat.add j (nat_lit 3))),
    bAnd(bIf(Nat.blt j (nat_lit 2), true, Nat.ble (nat_lit 3) a), ih)))))

private noncomputable def wordChk (j : Nat) (wd : List Int) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => chkZ j z ih) wd

private theorem chkZ_iff (j : Nat) (z : Int) (ih : Bool) :
    chkZ j z ih = true ↔
      (z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) ∧ (j < 2 ∨ 3 ≤ z.natAbs)) ∧ ih = true := by
  unfold chkZ
  simp only [strictB_eq, bAnd_eq, bIf_eq, Nat.blt_eq, Nat.ble_eq, icode_shiftRight, icode_pos]
  by_cases h0 : z = 0
  · simp [h0]
  by_cases h1 : z.natAbs ≤ 2 <;> by_cases h2 : z.natAbs < j + 3 <;> by_cases h3 : j < 2 <;>
    by_cases h4 : 3 ≤ z.natAbs <;> cases ih <;> simp [h0, h1, h2, h3, h4]

private theorem wordChk_iff (j : Nat) (wd : List Int) :
    wordChk j wd = true ↔
      ∀ z ∈ wd, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) ∧ (j < 2 ∨ 3 ≤ z.natAbs) := by
  induction wd with
  | nil => simp [wordChk]
  | cons z wd ih =>
    have h : wordChk j (z :: wd) = chkZ j z (wordChk j wd) := rfl
    rw [h, chkZ_iff, ih, List.forall_mem_cons]

private theorem wordsOK_cons (wd : List Int) (ws : List (List Int)) (j : Nat) :
    wordsOK (wd :: ws) j = (wordChk j wd && wordsOK ws (j + 1)) := by
  rw [← bAnd_eq]
  rfl

private theorem wordsOK_nil (j : Nat) : wordsOK [] j = true := rfl

theorem wordsOK_iff (ws : List (List Int)) (j : Nat) :
    wordsOK ws j = true ↔ ∀ i < ws.length, ∀ z ∈ ws.getD i [],
      z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + i + 3) ∧ (j + i < 2 ∨ 3 ≤ z.natAbs) := by
  induction ws generalizing j with
  | nil => simp [wordsOK_nil]
  | cons wd ws ih =>
    rw [wordsOK_cons, Bool.and_eq_true, wordChk_iff, ih (j + 1)]
    constructor
    · rintro ⟨h0, h1⟩ i hi z hz
      cases i with
      | zero =>
        have := h0 z (by simpa using hz)
        simpa using this
      | succ i =>
        have h := h1 i (by simpa using hi) z (by simpa using hz)
        have e : j + (i + 1) = j + 1 + i := by omega
        rw [e]
        exact h
    · intro h
      refine ⟨fun z hz => ?_, fun i hi z hz => ?_⟩
      · have := h 0 (by simp) z (by simpa using hz)
        simpa using this
      · have h' := h (i + 1) (by simpa using hi) z (by simpa using hz)
        have e : j + (i + 1) = j + 1 + i := by omega
        rw [e] at h'
        exact h'

theorem lenW_eq (ws : List (List Int)) : lenW ws = ws.length := by
  induction ws with
  | nil => rfl
  | cons wd ws ih =>
    show Nat.succ (lenW ws) = ws.length + 1
    rw [ih]

private theorem lettersFrom_nil (n : Nat) (gens : Int → Nat → Nat) (L : List (Nat → Nat)) :
    lettersFrom n gens L [] = L := rfl

private theorem lettersFrom_cons (n : Nat) (gens : Int → Nat → Nat) (L : List (Nat → Nat))
    (wd : List Int) (ws : List (List Int)) :
    lettersFrom n gens L (wd :: ws) =
      lettersFrom n gens (L ++ [wordFn gens L wd, finv n (wordFn gens L wd)]) ws := rfl

private theorem length_lettersFrom (n : Nat) (gens : Int → Nat → Nat) (ws : List (List Int)) :
    ∀ L : List (Nat → Nat), (lettersFrom n gens L ws).length = L.length + 2 * ws.length := by
  induction ws with
  | nil => intro L; rfl
  | cons wd ws ih =>
    intro L
    rw [lettersFrom_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem length_lettersFn (n : Nat) (gens : Int → Nat → Nat) (ws : List (List Int)) :
    (lettersFn n gens ws).length = 2 * ws.length := by
  rw [lettersFn, length_lettersFrom, List.length_nil, Nat.zero_add]

private theorem getD_append_left' {α : Type _} (L L' : List α) (d : α) {l : Nat}
    (h : l < L.length) : (L ++ L').getD l d = L.getD l d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right' {α : Type _} (L L' : List α) (d : α) {l : Nat}
    (h : L.length ≤ l) : (L ++ L').getD l d = L'.getD (l - L.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getD_append_pair (L : List (Nat → Nat)) (a b : Nat → Nat) (l : Nat) :
    (L ++ [a, b]).getD l id = if l < L.length then L.getD l id
      else if l = L.length then a else if l = L.length + 1 then b else id := by
  by_cases h : l < L.length
  · rw [if_pos h, getD_append_left' _ _ _ h]
  · rw [if_neg h, getD_append_right' _ _ _ (Nat.not_lt.1 h)]
    obtain ⟨k, rfl⟩ : ∃ k, l = L.length + k := ⟨l - L.length, by omega⟩
    rw [Nat.add_sub_cancel_left]
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp [List.getD_cons_succ]

private theorem isPermN_getD_append {n : Nat} {L : List (Nat → Nat)} {a b : Nat → Nat}
    (hL : ∀ l, IsPermN n (L.getD l id)) (ha : IsPermN n a) (hb : IsPermN n b) (l : Nat) :
    IsPermN n ((L ++ [a, b]).getD l id) := by
  rw [getD_append_pair]
  split
  · exact hL l
  · split
    · exact ha
    · split
      · exact hb
      · exact isPermN_id n

private theorem letFn_isPermN {n : Nat} {gens : Int → Nat → Nat}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) {L : List (Nat → Nat)}
    (hL : ∀ l, IsPermN n (L.getD l id)) {z : Int} (hz : z ≠ 0) : IsPermN n (letFn gens L z) := by
  unfold letFn
  split
  · exact hg z hz ‹_›
  · split <;> exact hL _

private theorem wordFn_isPermN {n : Nat} {gens : Int → Nat → Nat}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) {L : List (Nat → Nat)}
    (hL : ∀ l, IsPermN n (L.getD l id)) {wd : List Int} (hwd : ∀ z ∈ wd, z ≠ 0) :
    IsPermN n (wordFn gens L wd) := by
  induction wd with
  | nil => exact isPermN_id n
  | cons z wd ih =>
    exact (letFn_isPermN hg hL (hwd z List.mem_cons_self)).comp
      (ih fun y hy => hwd y (List.mem_cons_of_mem _ hy))

private theorem lettersFrom_isPermN {n : Nat} {gens : Int → Nat → Nat}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) (ws : List (List Int)) :
    ∀ (j : Nat) (L : List (Nat → Nat)), (∀ l, IsPermN n (L.getD l id)) → wordsOK ws j = true →
      ∀ l, IsPermN n ((lettersFrom n gens L ws).getD l id) := by
  induction ws with
  | nil => intro j L hL _ l; exact hL l
  | cons wd ws ih =>
    intro j L hL hws l
    rw [wordsOK_cons, Bool.and_eq_true, wordChk_iff] at hws
    rw [lettersFrom_cons]
    have hW : IsPermN n (wordFn gens L wd) := wordFn_isPermN hg hL fun z hz => (hws.1 z hz).1
    exact ih (j + 1) _ (isPermN_getD_append hL hW hW.finv) hws.2 l

theorem lettersFn_isPermN {n : Nat} {gens : Int → Nat → Nat}
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) {ws : List (List Int)}
    (hws : wordsOK ws 0 = true) {l : Nat} (hl : l < 2 * ws.length) :
    IsPermN n ((lettersFn n gens ws).getD l id) :=
  lettersFrom_isPermN hg ws 0 [] (fun l => by rw [List.getD_nil]; exact isPermN_id n) hws l

private theorem letterP_small (nw pm A Ai B Bi LT : Nat) :
    letterP nw pm A Ai B Bi LT 1 = A ∧ letterP nw pm A Ai B Bi LT (-1) = Ai ∧
      letterP nw pm A Ai B Bi LT 2 = B ∧ letterP nw pm A Ai B Bi LT (-2) = Bi :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem letterP_big (nw pm A Ai B Bi LT : Nat) {z : Int} (hz : 3 ≤ z.natAbs) :
    letterP nw pm A Ai B Bi LT z =
      blk LT nw pm (2 * (z.natAbs - 3) + if 0 ≤ z then 0 else 1) := by
  unfold letterP
  simp only [strictN_eq, nIf_eq, Nat.ble_eq, icode_shiftRight, icode_land_one]
  rw [if_neg (by omega)]
  congr 1

private theorem enc_lt_of_isPermN {n w : Nat} (hw : n < 2 ^ w) {g : Nat → Nat} (hg : IsPermN n g) :
    enc w g n < 2 ^ (n * w) := by
  rw [Nat.mul_comm n w]
  exact enc_lt fun i hi => Nat.lt_trans (hg.1 i hi) hw

private theorem fd_letterTable {n w : Nat} (hw : n < 2 ^ w) {L : List (Nat → Nat)}
    (hL : ∀ l, IsPermN n (L.getD l id)) {k l : Nat} (hl : l < k) {x : Nat} (hx : x < n) :
    fd w (fd (n * w) (enc (n * w) (fun l => enc w (L.getD l id) n) k) l) x = L.getD l id x := by
  rw [fd_enc (fun i _ => enc_lt_of_isPermN hw (hL i)) hl,
    fd_enc (fun i hi => Nat.lt_trans ((hL l).1 i hi) hw) hx]

private theorem fd_letterP {n w A Ai B Bi : Nat} {gens : Int → Nat → Nat} (hw : n < 2 ^ w)
    (hA : ∀ x < n, gens 1 x = fd w A x) (hAi : ∀ x < n, gens (-1) x = fd w Ai x)
    (hB : ∀ x < n, gens 2 x = fd w B x) (hBi : ∀ x < n, gens (-2) x = fd w Bi x)
    {L : List (Nat → Nat)} (hL : ∀ l, IsPermN n (L.getD l id)) {j : Nat} (hlen : L.length = 2 * j)
    {z : Int} (hz0 : z ≠ 0) (hz : z.natAbs ≤ 2 ∨ z.natAbs < j + 3) {LT : Nat}
    (hLT : LT = enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j)) {x : Nat} (hx : x < n) :
    fd w (letterP (n * w) (mask (n * w)) A Ai B Bi LT z) x = letFn gens L z x := by
  by_cases h : z.natAbs ≤ 2
  · have hz' : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
    have hlet : letFn gens L z x = gens z x := by
      unfold letFn
      rw [if_pos h]
    rw [hlet]
    obtain ⟨e1, e2, e3, e4⟩ := letterP_small (n * w) (mask (n * w)) A Ai B Bi LT
    rcases hz' with rfl | rfl | rfl | rfl
    · rw [e1, hA x hx]
    · rw [e2, hAi x hx]
    · rw [e3, hB x hx]
    · rw [e4, hBi x hx]
  · rw [letterP_big _ _ _ _ _ _ _ (by omega), blk_eq]
    have hzj : z.natAbs - 3 < j := by omega
    unfold letFn
    rw [if_neg h]
    by_cases hp : 0 ≤ z
    · have hp' : 0 < z := by omega
      rw [if_pos hp, if_pos hp', Nat.add_zero]
      change fd w (fd (n * w) LT (2 * (z.natAbs - 3))) x = _
      rw [hLT]
      exact fd_letterTable hw hL (by omega) hx
    · have hp' : ¬ 0 < z := by omega
      rw [if_neg hp, if_neg hp']
      change fd w (fd (n * w) LT (2 * (z.natAbs - 3) + 1)) x = _
      rw [hLT]
      exact fd_letterTable hw hL (by omega) hx

private theorem wordP_cons (n w m nw pm idn A Ai B Bi LT : Nat) (z : Int) (wd : List Int) :
    wordP n w m nw pm idn A Ai B Bi LT (z :: wd) =
      pcomp n w m (letterP nw pm A Ai B Bi LT z) (wordP n w m nw pm idn A Ai B Bi LT wd) := by
  show strictN _ _ = _
  rw [strictN_eq]
  rfl

private theorem wordP_eq {n w A Ai B Bi : Nat} {gens : Int → Nat → Nat} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hA : ∀ x < n, gens 1 x = fd w A x)
    (hAi : ∀ x < n, gens (-1) x = fd w Ai x) (hB : ∀ x < n, gens 2 x = fd w B x)
    (hBi : ∀ x < n, gens (-2) x = fd w Bi x)
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) {L : List (Nat → Nat)}
    (hL : ∀ l, IsPermN n (L.getD l id)) {j : Nat} (hlen : L.length = 2 * j) {LT : Nat}
    (hLT : LT = enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j)) (wd : List Int)
    (hwd : ∀ z ∈ wd, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3)) :
    wordP n w (mask w) (n * w) (mask (n * w)) (pidn n w) A Ai B Bi LT wd =
      enc w (wordFn gens L wd) n := by
  have hn24 : n ≤ 2 ^ 24 :=
    Nat.le_trans (Nat.le_of_lt hn16) (Nat.pow_le_pow_right (by decide) (by decide))
  have hn32 : n < 2 ^ 32 := Nat.lt_of_lt_of_le hn16 (Nat.pow_le_pow_right (by decide) (by decide))
  have hnw : n < 2 ^ w := Nat.lt_of_succ_lt hw
  induction wd with
  | nil =>
    show pidn n w = enc w (fun x => x) n
    exact pidn_eq hn24 (Nat.le_of_lt hnw)
  | cons z wd ih =>
    rw [wordP_cons, ih fun y hy => hwd y (List.mem_cons_of_mem _ hy), pcomp_eq hn32]
    have hW : IsPermN n (wordFn gens L wd) :=
      wordFn_isPermN hg hL fun y hy => (hwd y (List.mem_cons_of_mem _ hy)).1
    refine enc_congr fun i hi => ?_
    rw [fd_enc (fun x hx => Nat.lt_trans (hW.1 x hx) hnw) hi]
    exact fd_letterP hnw hA hAi hB hBi hL hlen (hwd z List.mem_cons_self).1
      (hwd z List.mem_cons_self).2 hLT (hW.1 i hi)

private theorem pinvS_enc {n w : Nat} (hw : n < 2 ^ w) {W : Nat → Nat} (hW : IsPermN n W) :
    pinvS n w (mask w) (enc w W n) = enc w (finv n W) n := by
  have hf : ∀ i < n, W i < 2 ^ w := fun i hi => Nat.lt_trans (hW.1 i hi) hw
  refine pinvS_eq (Nat.le_of_lt hw) ?_ ?_ ?_
  · intro i hi
    rw [fd_enc hf hi]
    exact hW.1 i hi
  · intro j hj
    obtain ⟨h1, h2⟩ := finv_spec hW hj
    refine ⟨h1, ?_⟩
    rw [fd_enc hf h1]
    exact h2
  · intro i hi
    rw [fd_enc hf hi]
    exact finv_apply hW hi

private theorem letterTable_append {n w : Nat} (hw : n < 2 ^ w) {L : List (Nat → Nat)} {j : Nat}
    (hlen : L.length = 2 * j) (hL : ∀ l, IsPermN n (L.getD l id)) {W Wi : Nat → Nat}
    (hW : IsPermN n W) (hWi : IsPermN n Wi) :
    (enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j) |||
        (enc w W n <<< (n * w * (j + j)))) ||| (enc w Wi n <<< (n * w * (j + j + 1))) =
      enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * (j + 1)) := by
  have hL' := isPermN_getD_append hL hW hWi
  have h0 : enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j) < 2 ^ (n * w * (j + j)) := by
    rw [← Nat.two_mul]
    exact enc_lt fun l _ => enc_lt_of_isPermN hw (hL l)
  have e0 : enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j) =
      enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * j) := by
    refine enc_congr fun l hl => ?_
    rw [getD_append_left' _ _ _ (by omega)]
  have eW : (L ++ [W, Wi]).getD (2 * j) id = W := by
    rw [getD_append_pair, if_neg (by omega), if_pos (by omega)]
  have eWi : (L ++ [W, Wi]).getD (2 * j + 1) id = Wi := by
    rw [getD_append_pair, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * j + 1) =
      enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j) + enc w W n * 2 ^ (n * w * (j + j)) := by
    rw [enc_succ, ← e0, eW, ← Nat.two_mul]
  have h2 : enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * (j + 1)) =
      enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * j + 1) +
        enc w Wi n * 2 ^ (n * w * (j + j + 1)) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, enc_succ, eWi,
      show 2 * j + 1 = j + j + 1 by omega]
  have h3 : enc (n * w) (fun l => enc w ((L ++ [W, Wi]).getD l id) n) (2 * j + 1) <
      2 ^ (n * w * (j + j + 1)) := by
    rw [show j + j + 1 = 2 * j + 1 by omega]
    exact enc_lt fun l _ => enc_lt_of_isPermN hw (hL' l)
  rw [lor_shiftLeft_eq_add h0, ← h1, lor_shiftLeft_eq_add h3, h2]

private theorem lettersP_cons (n w m nw pm idn A Ai B Bi : Nat) (wd : List Int)
    (ws : List (List Int)) (LT j : Nat) :
    lettersP n w m nw pm idn A Ai B Bi (wd :: ws) LT j =
      lettersP n w m nw pm idn A Ai B Bi ws
        ((LT ||| (wordP n w m nw pm idn A Ai B Bi LT wd <<< (nw * (j + j)))) |||
          (pinvS n w m (wordP n w m nw pm idn A Ai B Bi LT wd) <<< (nw * (j + j + 1))))
        (j + 1) := by
  have h : lettersP n w m nw pm idn A Ai B Bi (wd :: ws) LT j =
      strictN (wordP n w m nw pm idn A Ai B Bi LT wd) (fun T =>
        strictN (pinvS n w m T) (fun Ti =>
          lettersP n w m nw pm idn A Ai B Bi ws
            ((LT ||| (T <<< (nw * (j + j)))) ||| (Ti <<< (nw * (j + j + 1)))) (j + 1))) := rfl
  rw [h, strictN_eq, strictN_eq]

private theorem lettersP_nil (n w m nw pm idn A Ai B Bi LT j : Nat) :
    lettersP n w m nw pm idn A Ai B Bi [] LT j = LT := rfl

private theorem lettersP_gen {n w A Ai B Bi : Nat} {gens : Int → Nat → Nat} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hA : ∀ x < n, gens 1 x = fd w A x)
    (hAi : ∀ x < n, gens (-1) x = fd w Ai x) (hB : ∀ x < n, gens 2 x = fd w B x)
    (hBi : ∀ x < n, gens (-2) x = fd w Bi x)
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) (ws : List (List Int)) :
    ∀ (j : Nat) (L : List (Nat → Nat)) (LT : Nat), L.length = 2 * j →
      (∀ l, IsPermN n (L.getD l id)) →
      LT = enc (n * w) (fun l => enc w (L.getD l id) n) (2 * j) → wordsOK ws j = true →
      lettersP n w (mask w) (n * w) (mask (n * w)) (pidn n w) A Ai B Bi ws LT j =
        enc (n * w) (fun l => enc w ((lettersFrom n gens L ws).getD l id) n)
          (2 * (j + ws.length)) := by
  have hnw : n < 2 ^ w := Nat.lt_of_succ_lt hw
  induction ws with
  | nil =>
    intro j L LT _ _ hLT _
    rw [lettersP_nil, lettersFrom_nil, hLT, List.length_nil, Nat.add_zero]
  | cons wd ws ih =>
    intro j L LT hlen hL hLT hws
    subst hLT
    rw [wordsOK_cons, Bool.and_eq_true, wordChk_iff] at hws
    have hW : IsPermN n (wordFn gens L wd) :=
      wordFn_isPermN hg hL fun z hz => (hws.1 z hz).1
    have hwd : ∀ z ∈ wd, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs < j + 3) := fun z hz =>
      ⟨(hws.1 z hz).1, (hws.1 z hz).2.1⟩
    rw [lettersP_cons, wordP_eq hn16 hw hA hAi hB hBi hg hL hlen rfl wd hwd,
      pinvS_enc hnw hW, letterTable_append hnw hlen hL hW hW.finv, lettersFrom_cons,
      ih (j + 1) (L ++ [wordFn gens L wd, finv n (wordFn gens L wd)]) _
        (by simp only [List.length_append, List.length_cons, List.length_nil, hlen]; omega)
        (isPermN_getD_append hL hW hW.finv) rfl hws.2,
      List.length_cons, show j + (ws.length + 1) = j + 1 + ws.length by omega]

theorem lettersP_eq {n w A Ai B Bi : Nat} {gens : Int → Nat → Nat} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hA : ∀ x < n, gens 1 x = fd w A x) (hAi : ∀ x < n, gens (-1) x = fd w Ai x)
    (hB : ∀ x < n, gens 2 x = fd w B x) (hBi : ∀ x < n, gens (-2) x = fd w Bi x)
    (hg : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 → IsPermN n (gens z)) {ws : List (List Int)}
    (hws : wordsOK ws 0 = true) :
    lettersP n w (mask w) (n * w) (mask (n * w)) (pidn n w) A Ai B Bi ws 0 0 =
      enc (n * w) (fun l => enc w ((lettersFn n gens ws).getD l id) n) (2 * ws.length) := by
  have h := lettersP_gen hn16 hw hA hAi hB hBi hg ws 0 [] 0 rfl
    (fun l => by rw [List.getD_nil]; exact isPermN_id n) rfl hws
  rw [h, Nat.zero_add]
  rfl

end CFSG.KS.PK

end
