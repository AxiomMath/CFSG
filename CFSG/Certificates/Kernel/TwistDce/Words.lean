module

public import Certificates.Data.Kernel.TwistDce.Defs
public import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.TwDce.Words

open CFSG.KC.TwDce CFSG.KC.YModel

@[expose] noncomputable def lst (w : ℕ) : List ℕ := (List.range (wLen w)).map (wAt w)

theorem sN_eq (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl
theorem sB_eq (v : ℕ) (k : ℕ → Bool) : sB v k = k v := by cases v <;> rfl
theorem sW_eq (v : ℕ) (k : ℕ → WS) : sW v k = k v := by cases v <;> rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide
private theorem two_pow4 (p : ℕ) : 2 ^ (4 * p) = 16 ^ p := by
  rw [pow_mul]; norm_num

private theorem fld15 (x j : ℕ) : fld x (4 * j) 15 = x / 16 ^ j % 16 := by
  unfold fld
  show (x >>> (4 * j)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, two_pow4]

private theorem fld_or (a b o m : ℕ) : fld (a ||| b) o m = fld a o m ||| fld b o m := by
  unfold fld
  apply Nat.eq_of_testBit_eq
  intro i
  change (((a ||| b) >>> o) &&& m).testBit i = ((a >>> o) &&& m ||| (b >>> o) &&& m).testBit i
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight]
  cases (a.testBit (o + i)) <;> cases (b.testBit (o + i)) <;> cases m.testBit i <;> rfl

private theorem wAt_eq (w i : ℕ) : wAt w i = wStr w / 16 ^ i % 16 := by
  unfold wAt
  exact fld15 (wStr w) i

private theorem wAt_lt (w i : ℕ) : wAt w i < 16 := by
  rw [wAt_eq]; exact Nat.mod_lt _ (by norm_num)

private theorem lst_eq (w : ℕ) : lst w = (List.range (wLen w)).map (fun i => wStr w / 16 ^ i % 16) := by
  unfold lst
  exact List.map_congr_left fun i _ => wAt_eq w i

private theorem wLen_eq (w : ℕ) : wLen w = w % 2 ^ 32 := by
  unfold wLen
  show w &&& (2 ^ 32 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem wStr_eq (w : ℕ) : wStr w = w / 2 ^ 32 := by
  unfold wStr
  exact Nat.shiftRight_eq_div_pow w 32

private theorem wMk_eq {n s : ℕ} (hn : n < 2 ^ 32) : wMk n s = n + s * 2 ^ 32 := by
  unfold wMk
  show n ||| (s <<< 32) = _
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hn s, Nat.shiftLeft_eq, Nat.add_comm]

private theorem wLen_wMk {n s : ℕ} (hn : n < 2 ^ 32) : wLen (wMk n s) = n := by
  rw [wLen_eq, wMk_eq hn, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]

private theorem wStr_wMk {n s : ℕ} (hn : n < 2 ^ 32) : wStr (wMk n s) = s := by
  rw [wStr_eq, wMk_eq hn, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hn, Nat.zero_add]

private theorem wOK_iff (w : ℕ) : wOK w = true ↔ wStr w < 16 ^ wLen w := by
  unfold wOK
  show Nat.blt _ (1 <<< (4 * wLen w)) = true ↔ _
  rw [Nat.blt_eq, Nat.shiftLeft_eq, Nat.one_mul, two_pow4]

private theorem lst_wMk {n s : ℕ} (hn : n < 2 ^ 32) :
    lst (wMk n s) = (List.range n).map (fun i => s / 16 ^ i % 16) := by
  rw [lst_eq, wLen_wMk hn, wStr_wMk hn]

private theorem wMk_spec {n s : ℕ} (hn : n < 2 ^ 32) (hs : s < 16 ^ n) :
    wLen (wMk n s) = n ∧ wOK (wMk n s) = true ∧
      lst (wMk n s) = (List.range n).map (fun i => s / 16 ^ i % 16) :=
  ⟨wLen_wMk hn, (wOK_iff _).2 (by rw [wStr_wMk hn, wLen_wMk hn]; exact hs), lst_wMk hn⟩

private theorem shl_div_le {j a : ℕ} (s : ℕ) (h : j ≤ a) : s * 16 ^ a / 16 ^ j = s * 16 ^ (a - j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, Nat.add_sub_cancel_left, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by positivity)]

private theorem shl_div_ge {j a : ℕ} (s : ℕ) (h : a ≤ j) : s * 16 ^ a / 16 ^ j = s / 16 ^ (j - a) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, Nat.add_sub_cancel_left, mul_comm (16 ^ a), Nat.mul_div_mul_right _ _ (by positivity)]

private theorem term_field {c : ℕ} (hc : c < 16) (i j : ℕ) :
    c * 16 ^ i / 16 ^ j % 16 = if i = j then c else 0 := by
  split_ifs with h
  · subst h
    rw [Nat.mul_div_cancel _ (by positivity), Nat.mod_eq_of_lt hc]
  · rcases lt_or_gt_of_ne h with h | h
    · rw [shl_div_ge _ h.le, Nat.div_eq_of_lt (lt_of_lt_of_le hc (by
        calc 16 = 16 ^ 1 := by norm_num
          _ ≤ 16 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) (by omega)))]
    · rw [shl_div_le _ h.le]
      obtain ⟨d, hd⟩ : ∃ d, i - j = d + 1 := ⟨i - j - 1, by omega⟩
      rw [hd, pow_succ, ← mul_assoc, Nat.mul_mod_left]

private theorem fld_or' (a b j : ℕ) :
    (a ||| b) / 16 ^ j % 16 = a / 16 ^ j % 16 ||| b / 16 ^ j % 16 := by
  rw [← fld15, ← fld15, ← fld15, fld_or]

private theorem or_lt16 {x y n : ℕ} (hx : x < 16 ^ n) (hy : y < 16 ^ n) : x ||| y < 16 ^ n := by
  rw [← two_pow4] at hx hy ⊢
  exact Nat.or_lt_two_pow hx hy

private theorem term_lt {c p n : ℕ} (hc : c < 16) (hp : p < n) : c * 16 ^ p < 16 ^ n :=
  calc c * 16 ^ p < 16 * 16 ^ p := Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = 16 ^ (p + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 16 ^ n := Nat.pow_le_pow_right (by norm_num) hp

private theorem land15 (s : ℕ) : Nat.land s 15 = s % 16 := by
  show s &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

private theorem shr4 (s : ℕ) : Nat.shiftRight s 4 = s / 16 := by
  rw [show Nat.shiftRight s 4 = s >>> 4 from rfl, Nat.shiftRight_eq_div_pow]

private theorem fld_ones (x o m : ℕ) : fld x o (ones m) = x >>> o % 2 ^ m := by
  unfold fld ones
  show (x >>> o) &&& ((1 <<< m) - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

private noncomputable def revLoop (w n m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (wAt w i) (Nat.mul 4 (Nat.sub (Nat.sub n 1) i)))) m

private theorem revLoop_succ (w n m : ℕ) :
    revLoop w n (m + 1) = revLoop w n m ||| wAt w m * 16 ^ (n - 1 - m) := by
  show revLoop w n m ||| (wAt w m <<< (4 * (n - 1 - m))) = _
  rw [Nat.shiftLeft_eq, two_pow4]

private theorem revLoop_prop (w n : ℕ) : ∀ m, m ≤ n → revLoop w n m < 16 ^ n ∧
    ∀ j, revLoop w n m / 16 ^ j % 16 = if j < n ∧ n - 1 - j < m then wAt w (n - 1 - j) else 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, fun j => ?_⟩
    · show 0 < 16 ^ n
      positivity
    · show 0 / 16 ^ j % 16 = _
      simp
  | succ m ih =>
    intro hm
    obtain ⟨hb, hf⟩ := ih (by omega)
    rw [revLoop_succ]
    refine ⟨or_lt16 hb (term_lt (wAt_lt w m) (by omega)), fun j => ?_⟩
    rw [fld_or', hf j, term_field (wAt_lt w m)]
    by_cases h1 : n - 1 - m = j
    · subst h1
      have h2 : ¬ (n - 1 - (n - 1 - m) < m) := by omega
      have e : n - 1 - (n - 1 - m) = m := by omega
      rw [if_pos rfl, if_neg (fun h => h2 h.2), if_pos ⟨by omega, by omega⟩, e, Nat.zero_or]
    · have h3 : (j < n ∧ n - 1 - j < m + 1) ↔ (j < n ∧ n - 1 - j < m) := by omega
      rw [if_neg h1, Nat.or_zero]
      simp only [h3]

private noncomputable def thLoop (THM w n m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (thL THM (wAt w i)) (Nat.mul 4 i))) m

private theorem thL_lt (THM c : ℕ) : thL THM c < 16 := by
  unfold thL
  show fld THM (4 * c) 15 < 16
  rw [fld15]; exact Nat.mod_lt _ (by norm_num)

private theorem thLoop_succ (THM w n m : ℕ) :
    thLoop THM w n (m + 1) = thLoop THM w n m ||| thL THM (wAt w m) * 16 ^ m := by
  show thLoop THM w n m ||| (thL THM (wAt w m) <<< (4 * m)) = _
  rw [Nat.shiftLeft_eq, two_pow4]

private theorem thLoop_prop (THM w n : ℕ) : ∀ m, m ≤ n → thLoop THM w n m < 16 ^ n ∧
    ∀ j, thLoop THM w n m / 16 ^ j % 16 = if j < m then thL THM (wAt w j) else 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨?_, fun j => ?_⟩
    · show 0 < 16 ^ n
      positivity
    · show 0 / 16 ^ j % 16 = _
      simp
  | succ m ih =>
    intro hm
    obtain ⟨hb, hf⟩ := ih (by omega)
    rw [thLoop_succ]
    refine ⟨or_lt16 hb (term_lt (thL_lt THM _) (by omega)), fun j => ?_⟩
    rw [fld_or', hf j, term_field (thL_lt THM _)]
    by_cases h1 : m = j
    · subst h1
      rw [if_pos rfl, if_neg (by omega), if_pos (by omega), Nat.zero_or]
    · have h3 : (j < m + 1) ↔ (j < m) := by omega
      rw [if_neg h1, Nat.or_zero]
      simp only [h3]

private theorem inH_loop (w n : ℕ) :
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (Nat.blt (wAt w i) 10)) n) = true ↔ ∀ i < n, wAt w i < 10 := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB _ (Nat.blt (wAt w n) 10) = true ↔ _
    rw [andB_iff, ih, Nat.blt_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem inT_loop (THM w n : ℕ) :
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (andB (Nat.blt (wAt w i) 10)
        (Nat.blt (thL THM (wAt w i)) 10))) n) = true ↔
      ∀ i < n, wAt w i < 10 ∧ thL THM (wAt w i) < 10 := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB _ (andB (Nat.blt (wAt w n) 10) (Nat.blt (thL THM (wAt w n)) 10)) = true ↔ _
    rw [andB_iff, ih, andB_iff, Nat.blt_eq, Nat.blt_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

private theorem digs_succ (s n : ℕ) : (List.range (n + 1)).map (fun i => s / 16 ^ i % 16) =
    s % 16 :: (List.range n).map (fun i => (s / 16) / 16 ^ i % 16) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    show s / 16 ^ (i + 1) % 16 = _
    rw [pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

private theorem evP_loop (F : ℕ → ℕ) : ∀ (n s x : ℕ),
    (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ x => x)
      (fun _ ih s x => sN (fieldAt 32 (F (Nat.land s 15)) x) (fun y =>
        sN (Nat.shiftRight s 4) (fun s' => ih s' y))) n) s x =
    ((List.range n).map (fun i => s / 16 ^ i % 16)).foldl
      (fun p c => fieldAt 32 (F c) p) x := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    intro s x
    rw [digs_succ, List.foldl_cons]
    simp only [Nat.rec_add_one, sN_eq] at ih ⊢
    rw [ih, land15, shr4]

private theorem isOne_loop (F : ℕ → ℕ) (BS w : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (sB (fld BS (Nat.mul 16 i) 65535) (fun b =>
        Nat.beq (evP F w b) b))) n) = true →
    ∀ i < n, evP F w (fld BS (16 * i) 65535) = fld BS (16 * i) 65535 := by
  intro n
  induction n with
  | zero => intro _ i hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro h i hi
    change andB _ (sB (fld BS (Nat.mul 16 n) 65535) (fun b => Nat.beq (evP F w b) b)) = true at h
    rw [andB_iff, sB_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.1 i hi
    · exact Nat.eq_of_beq_eq_true h.2

private theorem wsMk_eq {k f J : ℕ} (hk : k < 256) (hf : f < 2) :
    wsMk k f J = k + f * 256 + J * 65536 := by
  unfold wsMk
  show (k ||| (f <<< 8)) ||| (J <<< 16) = _
  have h1 : k ||| (f <<< 8) = f <<< 8 + k := by
    rw [Nat.or_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt (by simpa using hk) f).symm
  have h2 : f <<< 8 + k < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [h1, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h2 J, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  norm_num
  ring

theorem length_lst (w : ℕ) : (lst w).length = wLen w := by
  simp [lst]

theorem wLen_lt (w : ℕ) : wLen w < 2 ^ 32 := by
  rw [wLen_eq]; exact Nat.mod_lt _ (by positivity)

theorem lst_zero : lst 0 = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [length_lst, wLen_eq]; rfl

theorem wOK_zero : wOK 0 = true := by
  rw [wOK_iff, wStr_eq]
  simp

theorem wCat_spec {a b : ℕ} (ha : wOK a = true) (hb : wOK b = true) (h : wLen a + wLen b < 2 ^ 32) :
    wLen (wCat a b) = wLen a + wLen b ∧ wOK (wCat a b) = true ∧ lst (wCat a b) = lst a ++ lst b := by
  have hwc : wCat a b = wMk (wLen a + wLen b) (wStr a ||| (wStr b <<< (4 * wLen a))) := rfl
  have ha' := (wOK_iff a).1 ha
  have hb' := (wOK_iff b).1 hb
  have hsh : wStr b <<< (4 * wLen a) = wStr b * 16 ^ wLen a := by
    rw [Nat.shiftLeft_eq, two_pow4]
  have hlt2 : wStr a ||| (wStr b <<< (4 * wLen a)) < 16 ^ (wLen a + wLen b) := by
    apply or_lt16
    · exact lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by norm_num) (by omega))
    · rw [hsh, pow_add]
      calc wStr b * 16 ^ wLen a < 16 ^ wLen b * 16 ^ wLen a :=
            Nat.mul_lt_mul_of_pos_right hb' (by positivity)
        _ = 16 ^ wLen a * 16 ^ wLen b := mul_comm _ _
  obtain ⟨h1, h2, _⟩ := wMk_spec h hlt2
  refine ⟨by rw [hwc]; exact h1, by rw [hwc]; exact h2, ?_⟩
  rw [hwc, lst_wMk h, lst_eq a, lst_eq b, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    rw [hsh, fld_or']
    have h0 : wStr b * 16 ^ wLen a / 16 ^ i % 16 = 0 := by
      rw [shl_div_le _ (by omega)]
      obtain ⟨d, hd⟩ : ∃ d, wLen a - i = d + 1 := ⟨wLen a - i - 1, by omega⟩
      rw [hd, pow_succ, ← mul_assoc, Nat.mul_mod_left]
    rw [h0, Nat.or_zero]
  · apply List.map_congr_left
    intro k _
    show (wStr a ||| (wStr b <<< (4 * wLen a))) / 16 ^ (wLen a + k) % 16 = _
    rw [hsh, fld_or', shl_div_ge _ (by omega), Nat.add_sub_cancel_left,
      Nat.div_eq_of_lt (lt_of_lt_of_le ha' (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.zero_mod, Nat.zero_or]

theorem wRev_spec (w : ℕ) :
    wLen (wRev w) = wLen w ∧ wOK (wRev w) = true ∧ lst (wRev w) = (lst w).reverse := by
  have hn := wLen_lt w
  have hwr : wRev w = wMk (wLen w) (revLoop w (wLen w) (wLen w)) := by
    unfold wRev
    rw [sN_eq]
    rfl
  obtain ⟨hb, hf⟩ := revLoop_prop w (wLen w) (wLen w) le_rfl
  obtain ⟨h1, h2, _⟩ := wMk_spec hn hb
  refine ⟨by rw [hwr]; exact h1, by rw [hwr]; exact h2, ?_⟩
  rw [hwr, lst_wMk hn]
  apply List.ext_getElem
  · simp [length_lst]
  · intro i hi1 hi2
    have hi : i < wLen w := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, lst, List.length_map,
      List.length_range]
    rw [hf i, if_pos ⟨hi, by omega⟩]

theorem wTh_spec (THM w : ℕ) :
    wLen (wTh THM w) = wLen w ∧ wOK (wTh THM w) = true ∧ lst (wTh THM w) = (lst w).map (thL THM) := by
  have hn := wLen_lt w
  have hwr : wTh THM w = wMk (wLen w) (thLoop THM w (wLen w) (wLen w)) := by
    unfold wTh
    rw [sN_eq]
    rfl
  obtain ⟨hb, hf⟩ := thLoop_prop THM w (wLen w) (wLen w) le_rfl
  obtain ⟨h1, h2, _⟩ := wMk_spec hn hb
  refine ⟨by rw [hwr]; exact h1, by rw [hwr]; exact h2, ?_⟩
  rw [hwr, lst_wMk hn]
  apply List.ext_getElem
  · simp [length_lst]
  · intro i hi1 hi2
    have hi : i < wLen w := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, lst, List.length_map, List.length_range]
    rw [hf i, if_pos hi]

theorem wOne_spec {c : ℕ} (hc : c < 16) : wLen (wOne c) = 1 ∧ wOK (wOne c) = true ∧ lst (wOne c) = [c] := by
  obtain ⟨h1, h2, h3⟩ := wMk_spec (n := 1) (s := c) (by norm_num) (by simpa using hc)
  refine ⟨h1, h2, ?_⟩
  change lst (wMk 1 c) = _
  rw [h3]
  simp [Nat.mod_eq_of_lt hc]

theorem hWord_spec (J : ℕ) : wLen (hWord J) < 2 ^ 16 ∧ wOK (hWord J) = true := by
  have hn : Nat.land J 65535 < 2 ^ 16 := by
    show J &&& (2 ^ 16 - 1) < _
    rw [Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (by positivity)
  have hw : hWord J = wMk (Nat.land J 65535)
      (fld J 16 (ones (4 * Nat.land J 65535))) := by
    unfold hWord
    rw [sN_eq]
    rfl
  have hn32 : Nat.land J 65535 < 2 ^ 32 := lt_trans hn (by norm_num)
  have hb : fld J 16 (ones (4 * Nat.land J 65535)) < 16 ^ Nat.land J 65535 := by
    rw [fld_ones, ← two_pow4]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨h1, h2, _⟩ := wMk_spec hn32 hb
  rw [hw]
  exact ⟨by rw [h1]; exact hn, h2⟩

theorem wInH_spec {w : ℕ} (h : wInH w = true) : wOK w = true ∧ ∀ c ∈ lst w, c < 10 := by
  unfold wInH at h
  rw [andB_iff] at h
  refine ⟨h.1, ?_⟩
  have := (inH_loop w (wLen w)).1 h.2
  intro c hc
  simp only [lst, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact this i hi

theorem wInT_spec {THM w : ℕ} (h : wInT THM w = true) :
    wOK w = true ∧ ∀ c ∈ lst w, c < 10 ∧ thL THM c < 10 := by
  unfold wInT at h
  rw [andB_iff] at h
  refine ⟨h.1, ?_⟩
  have := (inT_loop THM w (wLen w)).1 h.2
  intro c hc
  simp only [lst, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact this i hi

theorem evP_eq (F : ℕ → ℕ) (w x : ℕ) :
    evP F w x = (lst w).foldl (fun p c => fieldAt 32 (F c) p) x := by
  rw [lst_eq]
  exact evP_loop F (wLen w) (wStr w) x

theorem isOne_spec {F : ℕ → ℕ} {BS NB w : ℕ} (h : isOne F BS NB w = true) :
    Even (lst w).length ∧ ∀ i < NB, (lst w).foldl (fun p c => fieldAt 32 (F c) p)
      (fld BS (16 * i) 65535) = fld BS (16 * i) 65535 := by
  unfold isOne at h
  rw [sB_eq, andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun i hi => ?_⟩
  · rw [length_lst]
    have h3 : wLen w &&& 1 = 0 := Nat.eq_of_beq_eq_true h1
    rw [Nat.and_one_is_mod] at h3
    exact Nat.even_iff.2 h3
  · rw [← evP_eq]
    exact isOne_loop F BS w NB h2 i hi

theorem wsMk_spec {k f : ℕ} (hk : k < 256) (hf : f < 2) (J : ℕ) :
    wsK (wsMk k f J) = k ∧ wsFail (wsMk k f J) = f ∧ wsJ (wsMk k f J) = J := by
  rw [wsMk_eq hk hf]
  refine ⟨?_, ?_, ?_⟩
  · unfold wsK
    show _ &&& (2 ^ 8 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · unfold wsFail fld
    show ((_ : ℕ) >>> 8) &&& (2 ^ 1 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    omega
  · unfold wsJ
    show (_ : ℕ) >>> 16 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega

theorem fld_lt_succ (x o m : ℕ) : fld x o m < m + 1 :=
  Nat.lt_succ_of_le (Nat.and_le_right (n := x >>> o) (m := m))

theorem wsFail_lt (s : ℕ) : wsFail s < 2 := fld_lt_succ s 8 1

theorem dN1_lt (d : ℕ) : dN1 d < 256 := fld_lt_succ d 4 255

theorem dN2_lt (d : ℕ) : dN2 d < 256 := fld_lt_succ d 12 255

end CFSG.Certificates.TwDce.Words

end
