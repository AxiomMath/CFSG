module

public import Certificates.Data.Kernel.TwistDce2.Defs
public import CFSG.Certificates.Kernel.TwistDce.Words
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.TwDce2.Words

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange andB
open CFSG.KC (andB)
open CFSG.KC.TwDce2 CFSG.KC.YModel
open CFSG.Certificates.TwDce.Words hiding evP_eq isOne_spec wsMk_spec wsFail_lt dN1_lt dN2_lt
  andB_iff

theorem kandB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

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

private theorem lst_eq (w : ℕ) :
    lst w = (List.range (wLen w)).map (fun i => wStr w / 16 ^ i % 16) := by
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
  rw [wStr_eq, wMk_eq hn, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hn,
    Nat.zero_add]

private theorem wOK_iff (w : ℕ) : wOK w = true ↔ wStr w < 16 ^ wLen w := by
  unfold wOK
  show Nat.blt _ (1 <<< (4 * wLen w)) = true ↔ _
  rw [Nat.blt_eq, Nat.shiftLeft_eq, Nat.one_mul, two_pow4]

private theorem lst_wMk {n s : ℕ} (hn : n < 2 ^ 32) :
    lst (wMk n s) = (List.range n).map (fun i => s / 16 ^ i % 16) := by
  rw [lst_eq, wLen_wMk hn, wStr_wMk hn]

private theorem shl_div_le {j a : ℕ} (s : ℕ) (h : j ≤ a) :
    s * 16 ^ a / 16 ^ j = s * 16 ^ (a - j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, Nat.add_sub_cancel_left, Nat.mul_left_comm, Nat.mul_div_cancel_left _ (by positivity)]

private theorem shl_div_ge {j a : ℕ} (s : ℕ) (h : a ≤ j) :
    s * 16 ^ a / 16 ^ j = s / 16 ^ (j - a) := by
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

theorem ivL_lt (INVM c : ℕ) : ivL INVM c < 16 := by
  unfold ivL
  show fld INVM (4 * c) 15 < 16
  rw [fld15]; exact Nat.mod_lt _ (by norm_num)

private noncomputable def invLoop (INVM w n m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (ivL INVM (wAt w i))
      (Nat.mul 4 (Nat.sub (Nat.sub n 1) i)))) m

private theorem invLoop_succ (INVM w n m : ℕ) :
    invLoop INVM w n (m + 1) = invLoop INVM w n m ||| ivL INVM (wAt w m) * 16 ^ (n - 1 - m) := by
  show invLoop INVM w n m ||| (ivL INVM (wAt w m) <<< (4 * (n - 1 - m))) = _
  rw [Nat.shiftLeft_eq, two_pow4]

private theorem invLoop_prop (INVM w n : ℕ) : ∀ m, m ≤ n → invLoop INVM w n m < 16 ^ n ∧
    ∀ j, invLoop INVM w n m / 16 ^ j % 16 =
      if j < n ∧ n - 1 - j < m then ivL INVM (wAt w (n - 1 - j)) else 0 := by
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
    rw [invLoop_succ]
    refine ⟨or_lt16 hb (term_lt (ivL_lt INVM _) (by omega)), fun j => ?_⟩
    rw [fld_or', hf j, term_field (ivL_lt INVM _)]
    by_cases h1 : n - 1 - m = j
    · subst h1
      have h2 : ¬ (n - 1 - (n - 1 - m) < m) := by omega
      have e : n - 1 - (n - 1 - m) = m := by omega
      rw [if_pos rfl, if_neg (fun h => h2 h.2), if_pos ⟨by omega, by omega⟩, e, Nat.zero_or]
    · have h3 : (j < n ∧ n - 1 - j < m + 1) ↔ (j < n ∧ n - 1 - j < m) := by omega
      rw [if_neg h1, Nat.or_zero]
      simp only [h3]

theorem wInv_spec (INVM w : ℕ) : wLen (wInv INVM w) = wLen w ∧ wOK (wInv INVM w) = true ∧
    lst (wInv INVM w) = (lst w).reverse.map (ivL INVM) := by
  have hn := wLen_lt w
  have hwr : wInv INVM w = wMk (wLen w) (invLoop INVM w (wLen w) (wLen w)) := by
    unfold wInv
    rw [sN_eq]
    rfl
  obtain ⟨hb, hf⟩ := invLoop_prop INVM w (wLen w) (wLen w) le_rfl
  refine ⟨by rw [hwr]; exact wLen_wMk hn,
    by rw [hwr, wOK_iff, wStr_wMk hn, wLen_wMk hn]; exact hb, ?_⟩
  rw [hwr, lst_wMk hn]
  apply List.ext_getElem
  · simp [length_lst]
  · intro i hi1 hi2
    have hi : i < wLen w := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, lst, List.length_map,
      List.length_range]
    rw [hf i, if_pos ⟨hi, by omega⟩]

private theorem below_loop (m w n : ℕ) :
    (Nat.rec (motive := fun _ => Bool) true
      (fun i acc => andB acc (Nat.blt (wAt w i) m)) n) = true ↔ ∀ i < n, wAt w i < m := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change andB _ (Nat.blt (wAt w n) m) = true ↔ _
    rw [kandB_iff, ih, Nat.blt_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem wBelow_spec {m w : ℕ} (h : wBelow m w = true) : wOK w = true ∧ ∀ c ∈ lst w, c < m := by
  unfold wBelow at h
  rw [kandB_iff] at h
  refine ⟨h.1, ?_⟩
  have := (below_loop m w (wLen w)).1 h.2
  intro c hc
  simp only [lst, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact this i hi

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
      (fun _ ih s x => sN (fieldAt 11 (F (Nat.land s 15)) x) (fun y =>
        sN (Nat.shiftRight s 4) (fun s' => ih s' y))) n) s x =
    ((List.range n).map (fun i => s / 16 ^ i % 16)).foldl
      (fun p c => fieldAt 11 (F c) p) x := by
  intro n
  induction n with
  | zero => intro s x; rfl
  | succ n ih =>
    intro s x
    rw [digs_succ, List.foldl_cons]
    simp only [Nat.rec_add_one, sN_eq] at ih ⊢
    rw [ih, land15, shr4]

theorem evP_eq (F : ℕ → ℕ) (w x : ℕ) :
    evP F w x = (lst w).foldl (fun p c => fieldAt 11 (F c) p) x := by
  rw [lst_eq]
  exact evP_loop F (wLen w) (wStr w) x

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
    rw [kandB_iff, sB_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h.1 i hi
    · exact Nat.eq_of_beq_eq_true h.2

theorem isOne_spec {F : ℕ → ℕ} {BS NB w : ℕ} (h : isOne F BS NB w = true) :
    ∀ i < NB, (lst w).foldl (fun p c => fieldAt 11 (F c) p) (fld BS (16 * i) 65535) =
      fld BS (16 * i) 65535 := by
  unfold isOne at h
  rw [sB_eq] at h
  intro i hi
  rw [← evP_eq]
  exact isOne_loop F BS w NB h i hi

private theorem wsMk_eq {k f J : ℕ} (hk : k < 4096) (hf : f < 2) :
    wsMk k f J = k + f * 4096 + J * 65536 := by
  unfold wsMk
  show (k ||| (f <<< 12)) ||| (J <<< 16) = _
  have h1 : k ||| (f <<< 12) = f <<< 12 + k := by
    rw [Nat.or_comm]; exact (Nat.shiftLeft_add_eq_or_of_lt (by simpa using hk) f).symm
  have h2 : f <<< 12 + k < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]; omega
  rw [h1, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt h2 J, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  norm_num
  ring

theorem wsMk_spec {k f : ℕ} (hk : k < 4096) (hf : f < 2) (J : ℕ) :
    wsK (wsMk k f J) = k ∧ wsFail (wsMk k f J) = f ∧ wsJ (wsMk k f J) = J := by
  rw [wsMk_eq hk hf]
  refine ⟨?_, ?_, ?_⟩
  · unfold wsK
    show _ &&& (2 ^ 12 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  · unfold wsFail fld
    show ((_ : ℕ) >>> 12) &&& (2 ^ 1 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
    omega
  · unfold wsJ
    show (_ : ℕ) >>> 16 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega

theorem wsFail_lt (s : ℕ) : wsFail s < 2 := fld_lt_succ s 12 1

theorem dN1_lt (d : ℕ) : dN1 d < 4096 := fld_lt_succ d 4 4095

theorem dN2_lt (d : ℕ) : dN2 d < 4096 := fld_lt_succ d 16 4095

theorem land4095_lt (J : ℕ) : Nat.land J 4095 < 4096 :=
  Nat.lt_succ_of_le (Nat.and_le_right (n := J) (m := 4095))

theorem wsBad_fail (a : ℕ) : wsFail (wsBad a).1 = 1 :=
  (wsMk_spec (by norm_num) (by norm_num) 0).2.1

end CFSG.Certificates.TwDce2.Words

end
