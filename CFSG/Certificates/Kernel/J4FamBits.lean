module

public import Certificates.Data.Kernel.J4Fam
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFam

public section

namespace CFSG.KC.J4Fam

open CFSG.Sporadic.J4.QT (compT actT idT rowsXor getD_compT actT_lt lenOK lenOK_of)
open CFSG.EvenSporadicStandard.J4Std.DataLocal (maskOf testBit_maskOf)

theorem testBit_lanesW_foldl (w : Nat) (F : Nat → Nat) (q : Nat) :
    ∀ (l : List Nat) (a : Nat), (l.foldl (fun acc j => acc ||| (F j <<< (w * j))) a).testBit q =
      (a.testBit q || l.any fun j => decide (w * j ≤ q) && (F j).testBit (q - w * j))
  | [], a => by simp
  | j :: l, a => by
    rw [List.foldl_cons, testBit_lanesW_foldl w F q l, Nat.testBit_or, Nat.testBit_shiftLeft,
      List.any_cons]
    simp only [ge_iff_le, Bool.or_assoc]

theorem testBit_lanesW (w : Nat) (F : Nat → Nat) (l : List Nat) (q : Nat) :
    (lanesW w F l).testBit q = l.any fun j => decide (w * j ≤ q) && (F j).testBit (q - w * j) := by
  unfold lanesW
  rw [testBit_lanesW_foldl]
  simp

theorem lanesW_bit {w : Nat} {F : Nat → Nat} (hF : ∀ j, F j < 2 ^ w) {l : List Nat} {j k : Nat}
    (hk : k < w) : (lanesW w F l).testBit (w * j + k) = (decide (j ∈ l) && (F j).testBit k) := by
  rw [testBit_lanesW]
  by_cases hj : j ∈ l
  · simp only [hj, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true]
    constructor
    · rintro ⟨j', -, hj'⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj'
      obtain ⟨h1, h2⟩ := hj'
      rcases lt_trichotomy j' j with hlt | rfl | hgt
      · exfalso
        have : w ≤ w * j + k - w * j' := by
          have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hlt)
          rw [Nat.mul_succ] at this
          omega
        rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hF j')
          (Nat.pow_le_pow_right (by norm_num) this))] at h2
        exact Bool.false_ne_true h2
      · rwa [Nat.add_sub_cancel_left] at h2
      · exfalso
        have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hgt)
        rw [Nat.mul_succ] at this
        omega
    · intro h
      refine ⟨j, hj, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, by rwa [Nat.add_sub_cancel_left]⟩
  · simp only [hj, decide_false, Bool.false_and]
    apply Bool.eq_false_iff.2
    intro h
    rw [List.any_eq_true] at h
    obtain ⟨j', hj', hb⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨h1, h2⟩ := hb
    rcases lt_trichotomy j' j with hlt | rfl | hgt
    · have : w ≤ w * j + k - w * j' := by
        have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hlt)
        rw [Nat.mul_succ] at this
        omega
      rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hF j')
        (Nat.pow_le_pow_right (by norm_num) this))] at h2
      exact Bool.false_ne_true h2
    · exact hj hj'
    · have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hgt)
      rw [Nat.mul_succ] at this
      omega

theorem lanesW_lt {w : Nat} {F : Nat → Nat} (hF : ∀ j, F j < 2 ^ w) {n : Nat} :
    lanesW w F (List.range n) < 2 ^ (w * n) := by
  apply Nat.lt_pow_two_of_testBit
  intro q hq
  rw [testBit_lanesW]
  apply Bool.eq_false_iff.2
  intro h
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, hb⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hjn := List.mem_range.1 hj
  have : w ≤ q - w * j := by
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt hjn)
    rw [Nat.mul_succ] at this
    omega
  rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hF j)
    (Nat.pow_le_pow_right (by norm_num) this))] at hb
  exact Bool.false_ne_true hb.2

@[expose] def bx (g : Nat → Bool) : Bool := (List.range 11).foldl (fun acc b => acc ^^ g b) false

theorem bx_congr {g g' : Nat → Bool} (h : ∀ b < 11, g b = g' b) : bx g = bx g' := by
  unfold bx
  have key : ∀ (l : List Nat) (a : Bool), (∀ b ∈ l, g b = g' b) →
      l.foldl (fun acc b => acc ^^ g b) a = l.foldl (fun acc b => acc ^^ g' b) a := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons b l ih =>
      intro a hl
      rw [List.foldl_cons, List.foldl_cons, hl b List.mem_cons_self]
      exact ih _ fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')
  exact key _ _ fun b hb => h b (List.mem_range.1 hb)

theorem testBit_xsel (f : Nat → Bool) (X : Nat → Nat) (q : Nat) :
    (xsel f X).testBit q = bx fun b => f b && (X b).testBit q := by
  unfold xsel bx
  have key : ∀ (l : List Nat) (a : Nat),
      (l.foldl (fun acc b => bif f b then acc ^^^ X b else acc) a).testBit q =
        l.foldl (fun acc b => acc ^^ (f b && (X b).testBit q)) (a.testBit q) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      cases f b <;> simp [Nat.testBit_xor]
  rw [key, Nat.zero_testBit]

theorem testBit_actT (t : List Nat) (c s : Nat) :
    (actT t c).testBit s = bx fun b => c.testBit b && (t.getD b 0).testBit s := by
  unfold actT rowsXor bx
  have key : ∀ (l : List Nat) (a : Nat),
      (l.foldl (fun acc j => if c.testBit j then acc ^^^ t.getD j 0 else acc) a).testBit s =
        l.foldl (fun acc b => acc ^^ (c.testBit b && (t.getD b 0).testBit s)) (a.testBit s) := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      cases c.testBit b <;> simp [Nat.testBit_xor]
  rw [key, Nat.zero_testBit]

theorem wordB_lt (t : List Nat) (b : Nat) : wordB t b < 2 ^ 11 := by
  apply Nat.lt_pow_two_of_testBit
  intro k hk
  unfold wordB
  rw [testBit_maskOf]
  simp only [List.mem_filter, List.mem_range, decide_eq_false_iff_not, not_and]
  intro h
  omega

theorem testBit_wordB (t : List Nat) {b k : Nat} (hk : k < 11) : (wordB t b).testBit k = tb t k b := by
  unfold wordB
  rw [testBit_maskOf]
  simp [hk]

theorem eq_of_bits {x y : Nat} (hx : x < 2 ^ 11) (hy : y < 2 ^ 11)
    (h : ∀ s < 11, x.testBit s = y.testBit s) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro s
  rcases Nat.lt_or_ge s 11 with hs | hs
  · exact h s hs
  · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hs)),
      Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hs))]

@[expose] def WT (t : List Nat) : Prop := t.length = 11 ∧ ∀ x ∈ t, x < 2 ^ 11

theorem WT_lenOK {t : List Nat} (h : WT t) : lenOK t = true := lenOK_of h.1 h.2

theorem WT_getD {t : List Nat} (h : WT t) (k : Nat) : t.getD k 0 < 2 ^ 11 := by
  by_cases hk : k < t.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h.2 _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    norm_num

theorem WT_compT {s t : List Nat} (hs : WT s) (ht : WT t) : WT (compT s t) := by
  refine ⟨by simp [compT, ht.1], fun x hx => ?_⟩
  simp only [compT, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact actT_lt (WT_lenOK hs) y

theorem WT_eq {s t : List Nat} (hs : WT s) (ht : WT t)
    (h : ∀ k < 11, ∀ b < 11, (s.getD k 0).testBit b = (t.getD k 0).testBit b) : s = t := by
  apply List.ext_getElem (by rw [hs.1, ht.1])
  intro k h1 h2
  have hk : k < 11 := hs.1 ▸ h1
  have := eq_of_bits (WT_getD hs k) (WT_getD ht k) (h k hk)
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

section Planes

variable {INV : List (List Nat)} (hW : ∀ j < 191, WT (INV.getD j []))
include hW

theorem ppPlane_bit {b j k : Nat} (hj : j < 191) (hk : k < 11) :
    (ppPlane INV b).testBit (11 * j + k) = tb (INV.getD j []) k b := by
  unfold ppPlane lanes
  rw [lanesW_bit (fun j => wordB_lt _ b) hk, testBit_wordB _ hk]
  simp [hj]

theorem ttPlane_bit {b s : Nat} (q : Nat) :
    (ttPlane INV b s).testBit q =
      (decide (q % 11 = 0) && decide (q / 11 < 191) && tb (INV.getD (q / 11) []) b s) := by
  have hF : ∀ j, (bif tb (INV.getD j []) b s then 1 else 0) < 2 ^ 11 := fun j => by
    cases tb (INV.getD j []) b s <;> simp
  have hq : q = 11 * (q / 11) + q % 11 := (Nat.div_add_mod q 11).symm
  unfold ttPlane lanes
  rw [hq, lanesW_bit hF (Nat.mod_lt _ (by norm_num)), ← hq]
  have hm : decide (q / 11 ∈ List.range 191) = decide (q / 11 < 191) := by simp
  rw [hm]
  have h1 : (1 : Nat).testBit (q % 11) = decide (q % 11 = 0) := by
    by_cases h : q % 11 = 0
    · rw [h]; rfl
    · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow h)]
      simp [h]
  cases hb : tb (INV.getD (q / 11) []) b s
  · simp only [cond_false, Nat.zero_testBit, Bool.and_false]
  · simp only [cond_true, h1, Bool.and_true, Bool.true_and, Bool.and_comm]

end Planes

theorem testBit_orFold (G : Nat → Nat) (q : Nat) :
    ∀ (l : List Nat) (a : Nat), (l.foldl (fun acc k => acc ||| G k) a).testBit q =
      (a.testBit q || l.any fun k => (G k).testBit q)
  | [], a => by simp
  | k :: l, a => by
    rw [List.foldl_cons, testBit_orFold G q l, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem testBit_one_eq (q : Nat) : (1 : Nat).testBit q = decide (q = 0) := by
  by_cases h : q = 0
  · rw [h]; rfl
  · rw [Nat.testBit_eq_false_of_lt (Nat.one_lt_two_pow h)]
    simp [h]

theorem testBit_REP (q : Nat) : REP.testBit q = (decide (q % 11 = 0) && decide (q / 11 < 191)) := by
  have hq : q = 11 * (q / 11) + q % 11 := (Nat.div_add_mod q 11).symm
  unfold REP lanes
  rw [hq, lanesW_bit (fun _ => by norm_num) (Nat.mod_lt _ (by norm_num)), ← hq, testBit_one_eq]
  simp [Bool.and_comm]

theorem testBit_spread (m q : Nat) : (spread m).testBit q =
    (decide (q % 11 = 0) && decide (q / 11 < 191) && m.testBit (q / 11)) := by
  have hF : ∀ j, (bif m.testBit j then 1 else 0) < 2 ^ 11 := fun j => by
    cases m.testBit j <;> simp
  have hq : q = 11 * (q / 11) + q % 11 := (Nat.div_add_mod q 11).symm
  unfold spread lanes
  rw [hq, lanesW_bit hF (Nat.mod_lt _ (by norm_num)), ← hq]
  have hm : decide (q / 11 ∈ List.range 191) = decide (q / 11 < 191) := by simp
  rw [hm]
  cases m.testBit (q / 11)
  · simp
  · simp only [cond_true, testBit_one_eq, Bool.and_true]
    exact Bool.and_comm _ _

theorem testBit_laneNZ (X q : Nat) : (laneNZ X).testBit q =
    ((List.range 11).any fun k => X.testBit (q + k) && REP.testBit q) := by
  unfold laneNZ
  rw [testBit_orFold, Nat.zero_testBit, Bool.false_or]
  congr 1
  funext k
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm k q]

theorem testBit_diffAll (P Q : Nat → Nat) (q : Nat) : (diffAll P Q).testBit q =
    ((List.range 11).any fun s => (P s).testBit q ^^ (Q s).testBit q) := by
  unfold diffAll
  rw [testBit_orFold, Nat.zero_testBit, Bool.false_or]
  congr 1
  funext s
  rw [Nat.testBit_xor]

theorem testBit_fill (Y q : Nat) : (fill Y).testBit q =
    ((List.range 11).any fun k => decide (k ≤ q) && Y.testBit (q - k)) := by
  unfold fill
  rw [testBit_lanesW]
  simp

theorem ppOK_spec {INV : List (List Nat)} {PP : List Nat} (h : ppOK INV PP = true) :
    ∀ b < 11, PP.getD b 0 = ppPlane INV b := by
  simp only [ppOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.2

theorem ttOK_spec {INV : List (List Nat)} {TT : List (List Nat)} (h : ttOK INV TT = true) :
    ∀ b < 11, ∀ s < 11, (TT.getD b []).getD s 0 = ttPlane INV b s := by
  simp only [ttOK, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem packW_lt (t : List Nat) : packW t < 2 ^ 121 := lanesW_lt (wordB_lt t)

theorem wall_field {INV : List (List Nat)} {WALL : Nat} (h : wallOK INV WALL = true) {p s : Nat}
    (hp : p < 191) (hs : s < 11) :
    (WALL >>> (121 * p + 11 * s)) &&& 2047 = wordB (INV.getD p []) s := by
  simp only [wallOK, beq_iff_eq] at h
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  rcases Nat.lt_or_ge k 11 with hk | hk
  · have h2047 : (2047 : Nat).testBit k = true := by
      rw [show (2047 : Nat) = 2 ^ 11 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simpa using hk
    rw [h2047, Bool.and_true, h, show 121 * p + 11 * s + k = 121 * p + (11 * s + k) by omega,
      lanesW_bit (fun p => packW_lt _) (by omega)]
    simp only [List.mem_range, hp, decide_true, Bool.true_and]
    unfold packW lanes
    rw [lanesW_bit (wordB_lt _) hk]
    simp [hs]
  · have h2047 : (2047 : Nat).testBit k = false := by
      rw [show (2047 : Nat) = 2 ^ 11 - 1 by rfl, Nat.testBit_two_pow_sub_one]; simpa using hk
    rw [h2047, Bool.and_false, Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (wordB_lt _ s)
      (Nat.pow_le_pow_right (by norm_num) hk))]

theorem testBit_ePlGo (WALL s : Nat) (q : Nat) :
    ∀ (row : List Nat) (j0 : Nat), (ePlGo WALL s row j0).testBit q =
      ((List.range row.length).any fun j => decide (11 * (j0 + j) ≤ q) &&
        ((WALL >>> (121 * row.getD j 0 + 11 * s)) &&& 2047).testBit (q - 11 * (j0 + j)))
  | [], _ => by simp [ePlGo]
  | p :: ps, j0 => by
    rw [ePlGo, Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ePlGo WALL s q ps (j0 + 1),
      List.length_cons, List.range_succ_eq_map, List.any_cons, List.any_map]
    simp only [Nat.add_zero, List.getD_cons_zero, ge_iff_le, Function.comp_def,
      List.getD_cons_succ, Nat.add_assoc, Nat.add_comm 1]

theorem ePl_eq (WALL : Nat) (row : List Nat) (s : Nat) :
    ePl WALL row s = lanesW 11 (fun j => (WALL >>> (121 * row.getD j 0 + 11 * s)) &&& 2047)
      (List.range row.length) := by
  apply Nat.eq_of_testBit_eq
  intro q
  unfold ePl
  rw [testBit_ePlGo, testBit_lanesW]
  simp

section Rows

variable {INV : List (List Nat)} (hW : ∀ j < 191, WT (INV.getD j []))
include hW

theorem aPl_bit {PP : List Nat} (hPP : ppOK INV PP = true) (t : List Nat) {s j k : Nat}
    (hj : j < 191) (hk : k < 11) :
    (aPl PP t s).testBit (11 * j + k) = ((compT t (INV.getD j [])).getD k 0).testBit s := by
  unfold aPl
  rw [testBit_xsel, getD_compT, testBit_actT]
  apply bx_congr
  intro b hb
  rw [ppOK_spec hPP b hb, ppPlane_bit hW hj hk]
  unfold tb
  exact Bool.and_comm _ _

theorem bPl_bit {TT : List (List Nat)} (hTT : ttOK INV TT = true) (t : List Nat) {s j k : Nat}
    (hs : s < 11) (hj : j < 191) (hk : k < 11) :
    (bPl TT t s).testBit (11 * j + k) = ((compT (INV.getD j []) t).getD k 0).testBit s := by
  unfold bPl
  rw [testBit_lanesW, getD_compT, testBit_actT]
  simp only [Nat.one_mul]
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  have key : ∀ k' < 11, k' ≤ 11 * j + k →
      (xsel (fun b => tb t k' b) fun b => (TT.getD b []).getD s 0).testBit (11 * j + k - k') =
        (decide (k' = k) && bx fun b => tb t k b && tb (INV.getD j []) b s) := by
    intro k' hk' hle
    rw [testBit_xsel]
    by_cases hkk : k' = k
    · subst hkk
      rw [show 11 * j + k' - k' = 11 * j by omega]
      simp only [decide_true, Bool.true_and]
      apply bx_congr
      intro b hb
      rw [ttOK_spec hTT b hb s hs, ttPlane_bit hW]
      simp [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 11), hj]
    · simp only [hkk, decide_false, Bool.false_and]
      unfold bx
      have h0 : ∀ b, ((TT.getD b []).getD s 0).testBit (11 * j + k - k') = false ∨ 11 ≤ b := by
        intro b
        rcases Nat.lt_or_ge b 11 with hb | hb
        · left
          rw [ttOK_spec hTT b hb s hs, ttPlane_bit hW]
          have : (11 * j + k - k') % 11 ≠ 0 := by omega
          simp [this]
        · exact Or.inr hb
      have key2 : ∀ (l : List Nat), (∀ b ∈ l, b < 11) → ∀ a,
          l.foldl (fun acc b => acc ^^ (tb t k' b &&
            ((TT.getD b []).getD s 0).testBit (11 * j + k - k'))) a = a := by
        intro l
        induction l with
        | nil => intro _ a; rfl
        | cons b l ih =>
          intro hl a
          rw [List.foldl_cons]
          rcases h0 b with h | h
          · rw [h, Bool.and_false, Bool.xor_false]
            exact ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) a
          · exact absurd (hl b List.mem_cons_self) (by omega)
      exact key2 _ (fun b hb => List.mem_range.1 hb) false
  constructor
  · rintro ⟨k', hk', hb⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rw [key k' (List.mem_range.1 hk') hb.1] at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    obtain ⟨-, rfl, hb⟩ := hb
    rw [← hb]
    apply bx_congr
    intro b _
    unfold tb
    rfl
  · intro h
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [key k hk (by omega)]
    simp only [decide_true, Bool.true_and]
    rw [← h]
    apply bx_congr
    intro b _
    unfold tb
    rfl

theorem ePl_bit {WALL : Nat} (hWl : wallOK INV WALL = true) {row : List Nat} {s j k : Nat}
    (hs : s < 11) (hj : j < row.length) (hk : k < 11) (hp : row.getD j 0 < 191) :
    (ePl WALL row s).testBit (11 * j + k) =
      ((INV.getD (row.getD j 0) []).getD k 0).testBit s := by
  rw [ePl_eq, lanesW_bit (fun j => by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [Nat.testBit_and, show (2047 : Nat) = 2 ^ 11 - 1 by rfl, Nat.testBit_two_pow_sub_one]
      simp; omega) hk, wall_field hWl hp hs, testBit_wordB _ hk]
  simp [hj, tb]

end Rows

theorem ptRowOK_spec {m i : Nat} :
    ∀ {row : List Nat} {j0 : Nat}, ptRowOK m i row j0 = true →
      j0 + row.length = 191 ∧ ∀ j < row.length,
        (j0 + j = i → row.getD j 0 = 191) ∧ (j0 + j ≠ i → m.testBit (j0 + j) = true →
          row.getD j 0 < 191) ∧ (j0 + j ≠ i → m.testBit (j0 + j) = false → row.getD j 0 = 0)
  | [], j0, h => by
    simp only [ptRowOK, beq_iff_eq] at h
    exact ⟨by simpa using h, fun j hj => by simp at hj⟩
  | x :: xs, j0, h => by
    simp only [ptRowOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ptRowOK_spec h2
    refine ⟨by simp at ih1 ⊢; omega, fun j hj => ?_⟩
    rcases j with _ | j
    · simp only [Nat.add_zero, List.getD_cons_zero]
      by_cases hji : j0 = i
      · subst hji
        simp only [beq_self_eq_true, cond_true, beq_iff_eq] at h1
        exact ⟨fun _ => h1, fun h => absurd rfl h, fun h => absurd rfl h⟩
      · have hb : (j0 == i) = false := by simpa using hji
        rw [hb, cond_false] at h1
        refine ⟨fun h => absurd h hji, fun _ hm => ?_, fun _ hm => ?_⟩
        · rw [hm, cond_true] at h1; simpa using h1
        · rw [hm, cond_false] at h1; simpa using h1
    · simp only [List.getD_cons_succ]
      have := ih2 j (by simpa using hj)
      rw [show j0 + (j + 1) = j0 + 1 + j by omega]
      exact this

theorem rowOK_spec {INV : List (List Nat)} {CML : List Nat} {PTL : List (List Nat)}
    {PTP PP : List Nat} {TT : List (List Nat)} {WALL i : Nat}
    (hW : ∀ j < 191, WT (INV.getD j [])) (hPP : ppOK INV PP = true) (hTT : ttOK INV TT = true)
    (hWl : wallOK INV WALL = true) (hi : i < 191)
    (h : rowOK INV CML PTL PTP PP TT WALL i = true) :
    CML.getD i 0 = maskOf ((List.range 191).filter fun j => comT (INV.getD i []) (INV.getD j [])) ∧
    (PTL.getD i []).length = 191 ∧ (∀ x ∈ PTL.getD i [], x < 256) ∧
    PTP.getD i 0 = packR (PTL.getD i []) ∧
    ∀ j < 191, (comT (INV.getD i []) (INV.getD j []) = true →
        (i = j → (PTL.getD i []).getD j 0 = 191) ∧
        (i ≠ j → (PTL.getD i []).getD j 0 < 191 ∧
          INV.getD ((PTL.getD i []).getD j 0) [] = compT (INV.getD i []) (INV.getD j []))) ∧
      (comT (INV.getD i []) (INV.getD j []) = false → (PTL.getD i []).getD j 0 = 0) := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hlt, hsp⟩, hpt⟩, hpp⟩, hpr⟩ := h
  set t := INV.getD i []
  set m := CML.getD i 0
  set row := PTL.getD i []
  have hWt : WT t := hW i hi
  have hcom : ∀ j < 191, m.testBit j = comT t (INV.getD j []) := by
    intro j hj
    have e := congrArg (fun x => x.testBit (11 * j)) hsp
    simp only [testBit_spread, Nat.testBit_xor, testBit_REP, testBit_laneNZ, testBit_diffAll,
      Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 11), hj, decide_true,
      Bool.true_and, Bool.and_true] at e
    rw [e]
    have hbits : ∀ k < 11, ∀ s < 11, (aPl PP t s).testBit (11 * j + k) =
        ((compT t (INV.getD j [])).getD k 0).testBit s ∧ (bPl TT t s).testBit (11 * j + k) =
        ((compT (INV.getD j []) t).getD k 0).testBit s := fun k hk s hs =>
      ⟨aPl_bit hW hPP t hj hk, bPl_bit hW hTT t hs hj hk⟩
    unfold comT
    by_cases heq : compT t (INV.getD j []) = compT (INV.getD j []) t
    · rw [heq, beq_self_eq_true, Bool.true_xor, Bool.not_eq_true', List.any_eq_false]
      intro k hk
      rw [Bool.not_eq_true, List.any_eq_false]
      intro s hs
      have hk' := List.mem_range.1 hk
      have hs' := List.mem_range.1 hs
      rw [(hbits k hk' s hs').1, (hbits k hk' s hs').2, heq]
      simp
    · have hne : (compT t (INV.getD j []) == compT (INV.getD j []) t) = false := by simpa using heq
      rw [hne, Bool.true_xor, Bool.not_eq_false', List.any_eq_true]
      by_contra hall
      apply heq
      apply WT_eq (WT_compT hWt (hW j hj)) (WT_compT (hW j hj) hWt)
      intro k hk s hs
      have := hbits k hk s hs
      rw [← this.1, ← this.2]
      by_contra hd
      apply hall
      refine ⟨k, List.mem_range.2 hk, ?_⟩
      rw [List.any_eq_true]
      exact ⟨s, List.mem_range.2 hs, by simpa using hd⟩
  obtain ⟨hlen, hrow⟩ := ptRowOK_spec hpt
  simp only [Nat.zero_add] at hlen hrow
  refine ⟨?_, hlen, ?_, hpp, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro j
    rw [testBit_maskOf]
    rcases Nat.lt_or_ge j 191 with hj | hj
    · rw [hcom j hj]
      simp [hj]
    · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hj))]
      simp only [List.mem_filter, List.mem_range]
      simp [show ¬ j < 191 by omega]
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    have := hrow j hj
    rw [List.getD_eq_getElem _ _ hj] at this
    by_cases hji : j = i
    · rw [this.1 hji]; norm_num
    · cases hm : m.testBit j
      · rw [this.2.2 hji hm]; norm_num
      · have := this.2.1 hji hm; omega
  · intro j hj
    have hr := hrow j (by omega)
    refine ⟨fun hc => ⟨fun hij => hr.1 hij.symm, fun hij => ?_⟩, fun hc => ?_⟩
    · have hm : m.testBit j = true := by rw [hcom j hj]; exact hc
      have hp := hr.2.1 (Ne.symm hij) hm
      refine ⟨hp, ?_⟩
      have hz : ∀ k < 11, ∀ s < 11, (aPl PP t s).testBit (11 * j + k) =
          (ePl WALL row s).testBit (11 * j + k) := by
        intro k hk s hs
        have e := congrArg (fun x => x.testBit (11 * j + k)) hpr
        simp only [Nat.testBit_and, Nat.zero_testBit] at e
        have hfill : (fill (spread m ^^^ (1 <<< (11 * i)))).testBit (11 * j + k) = true := by
          rw [testBit_fill, List.any_eq_true]
          refine ⟨k, List.mem_range.2 hk, ?_⟩
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨by omega, ?_⟩
          rw [show 11 * j + k - k = 11 * j by omega, Nat.testBit_xor, testBit_spread,
            Nat.one_shiftLeft, Nat.testBit_two_pow]
          simp [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by norm_num : 0 < 11), hj, hm,
            show 11 * i ≠ 11 * j by omega]
        rw [hfill, Bool.and_true, testBit_diffAll] at e
        simp only [List.any_eq_false, List.mem_range] at e
        have := e s hs
        revert this
        cases (aPl PP t s).testBit (11 * j + k) <;> cases (ePl WALL row s).testBit (11 * j + k) <;>
          simp
      apply (WT_eq (hW _ hp) (WT_compT hWt (hW j hj)) ?_).symm.symm
      intro k hk s hs
      rw [← ePl_bit hW hWl hs (by omega) hk hp, ← hz k hk s hs, aPl_bit hW hPP t hj hk]
    · have hm : m.testBit j = false := by rw [hcom j hj]; exact hc
      by_cases hji : j = i
      · exfalso
        subst hji
        have : comT t t = true := by unfold comT; simp
        rw [this] at hc
        exact Bool.noConfusion hc
      · exact hr.2.2 hji hm

theorem plOK_spec {PL : List Nat} (h : plOK PL = true) :
    ∀ b < 11, ∀ c < 2048, (PL.getD b 0).testBit c = c.testBit b := by
  simp only [plOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact h.2

theorem incr_spec : ∀ {l : List Nat}, incr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := incr_spec h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem eq_of_pairwise_lt : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 List.mem_cons_self) (by simp)
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 List.mem_cons_self) with e | ha
      · exact e
      · rcases List.mem_cons.1 ((h b).2 List.mem_cons_self) with e | hb
        · exact e.symm
        · have := List.rel_of_pairwise_cons h₂ ha
          have := List.rel_of_pairwise_cons h₁ hb
          omega
    subst hab
    congr 1
    refine eq_of_pairwise_lt (List.Pairwise.of_cons h₁) (List.Pairwise.of_cons h₂) fun x => ?_
    constructor
    · intro hx
      rcases List.mem_cons.1 ((h x).1 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (List.rel_of_pairwise_cons h₁ hx) (by omega)
      · exact e
    · intro hx
      rcases List.mem_cons.1 ((h x).2 (List.mem_cons_of_mem _ hx)) with e | e
      · exact absurd (List.rel_of_pairwise_cons h₂ hx) (by omega)
      · exact e

set_option exponentiation.threshold 2048 in
theorem fixRowOK_spec {INV : List (List Nat)} {FB : List Nat} {FLL : List (List Nat)}
    {PL : List Nat} {i : Nat} (hWt : WT (INV.getD i [])) (hPL : plOK PL = true)
    (h : fixRowOK INV FB FLL PL i = true) :
    (∀ c < 2048, (FB.getD i 0).testBit c = (actT (INV.getD i []) c == c)) ∧
      FLL.getD i [] = (List.range 2048).filter (FB.getD i 0).testBit := by
  simp only [fixRowOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  set t := INV.getD i []
  have hfix : ∀ c < 2048, (FB.getD i 0).testBit c = (actT t c == c) := by
    intro c hc
    rw [h1]
    unfold fixBits
    rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one, testBit_diffAll]
    simp only [show decide (c < 2048) = true from decide_eq_true hc, Bool.and_true, Bool.true_xor]
    have hs : ∀ s < 11, (xsel (fun b => tb t b s) (PL.getD · 0)).testBit c = (actT t c).testBit s := by
      intro s _
      rw [testBit_xsel, testBit_actT]
      apply bx_congr
      intro b hb
      rw [plOK_spec hPL b hb c hc]
      unfold tb
      exact Bool.and_comm _ _
    by_cases he : actT t c = c
    · rw [he, beq_self_eq_true]
      simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range]
      intro s hs'
      rw [hs s hs', plOK_spec hPL s hs' c hc, he]
      simp
    · have hne : (actT t c == c) = false := by simpa using he
      rw [hne]
      simp only [Bool.not_eq_false', List.any_eq_true, List.mem_range]
      by_contra hall
      apply he
      apply eq_of_bits (actT_lt (WT_lenOK hWt) c) (by omega)
      intro s hs'
      by_contra hd
      exact hall ⟨s, hs', by rw [hs s hs', plOK_spec hPL s hs' c hc]; simpa using hd⟩
  refine ⟨hfix, eq_of_pairwise_lt (incr_spec h2) (List.pairwise_lt_range.filter _) fun x => ?_⟩
  simp only [List.mem_filter, List.mem_range]
  constructor
  · intro hx
    refine ⟨h3 x hx, ?_⟩
    rw [← h4, testBit_maskOf]
    simpa using hx
  · rintro ⟨-, hb⟩
    rw [← h4, testBit_maskOf] at hb
    simpa using hb

end CFSG.KC.J4Fam
