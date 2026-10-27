module

public import CFSG.Certificates.Kernel.P0RankK.OrbComp
public import CFSG.Certificates.Kernel.P0RankK.VisIdx
public import CFSG.Certificates.Kernel.P0RankK.VisVisit
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank

@[expose] noncomputable def fixC (BT : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range 32).filter fun z => ∀ κ ∈ W, bAct BT κ (emb z) = emb z

theorem emb_zero' : emb 0 = 0 := colsAct_zero embCols

theorem emb_xor' (z z' : ℕ) : emb (z ^^^ z') = emb z ^^^ emb z' := colsAct_xor embCols z z'

theorem lamSpan_spec (h : lamSpan = true) : ∀ τ < 512, lamC τ < 16 ∧ lamZ τ < 32 ∧
    colsAct [1, 2, 12, 48] (lamC τ) ^^^ emb (lamZ τ) = τ := by
  intro τ hτ
  rw [lamSpan, List.all_eq_true] at h
  have h1 := h τ (List.mem_range.2 hτ)
  simp only [Bool.and_eq_true, Nat.blt_eq] at h1
  exact ⟨h1.1.1, h1.1.2, Nat.eq_of_beq_eq_true h1.2⟩

theorem lamBOK_spec {BT : ℕ} (h : lamBOK BT = true) :
    ∀ κ < 1024, ∀ l ∈ [1, 2, 12, 48], bAct BT κ l = l := by
  intro κ hκ l hl
  rw [lamBOK, List.all_eq_true] at h
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 (h κ (List.mem_range.2 hκ)) l hl)

theorem colsAct_fixed {f : ℕ → ℕ} (h0 : f 0 = 0)
    (hlin : ∀ x < 2 ^ 9, ∀ y < 2 ^ 9, f (x ^^^ y) = f x ^^^ f y) :
    ∀ (L : List ℕ), (∀ l ∈ L, l < 2 ^ 9 ∧ f l = l) → ∀ c, f (colsAct L c) = colsAct L c
  | [], _, _ => h0
  | l :: L, hL, c => by
    have ih := colsAct_fixed h0 hlin L (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) (c / 2)
    have hl := hL l List.mem_cons_self
    have hlt : colsAct L (c / 2) < 2 ^ 9 :=
      colsAct_lt (fun l' hl' => (hL l' (List.mem_cons_of_mem _ hl')).1) _
    simp only [colsAct]
    split_ifs
    · rw [hlin _ hl.1 _ hlt, hl.2, ih]
    · rw [hlin _ (Nat.two_pow_pos 9) _ hlt, h0, ih]

theorem Y_card_le' {BT : ℕ} (hlamB : lamBOK BT = true) (hlamS : lamSpan = true)
    (hB0 : ∀ κ < 2 ^ 10, bAct BT κ 0 = 0)
    (hBlin : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, ∀ y < 2 ^ 9,
      bAct BT κ (x ^^^ y) = bAct BT κ x ^^^ bAct BT κ y)
    {W Y : Finset ℕ} (hW10 : ∀ κ ∈ W, κ < 2 ^ 10) (hY9 : ∀ τ ∈ Y, τ < 2 ^ 9)
    (hYW : ∀ τ ∈ Y, ∀ κ ∈ W, bAct BT κ τ = τ) : Y.card ≤ 16 * (fixC BT W).card := by
  classical
  have hspan := lamSpan_spec hlamS
  have hL : ∀ κ ∈ W, ∀ c, bAct BT κ (colsAct [1, 2, 12, 48] c) = colsAct [1, 2, 12, 48] c := by
    intro κ hκ c
    have hκ' : κ < 1024 := lt_of_lt_of_eq (hW10 κ hκ) (by norm_num)
    refine colsAct_fixed (hB0 κ (hW10 κ hκ)) (hBlin κ (hW10 κ hκ)) _
      (fun l hl => ⟨?_, lamBOK_spec hlamB κ hκ' l hl⟩) c
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> norm_num
  have h512 : ∀ τ ∈ Y, τ < 512 := fun τ hτ => lt_of_lt_of_eq (hY9 τ hτ) (by norm_num)
  let f : ℕ → ℕ × ℕ := fun τ => (lamC τ, lamZ τ)
  have hmaps : Set.MapsTo f ↑Y ↑(Finset.range 16 ×ˢ fixC BT W) := by
    intro τ hτ
    obtain ⟨hc, hz, heq⟩ := hspan τ (h512 τ hτ)
    change f τ ∈ Finset.range 16 ×ˢ fixC BT W
    rw [Finset.mem_product]
    refine ⟨Finset.mem_range.2 hc, Finset.mem_filter.2 ⟨Finset.mem_range.2 hz, fun κ hκ => ?_⟩⟩
    have hκ10 := hW10 κ hκ
    have hlt1 : colsAct [1, 2, 12, 48] (lamC τ) < 2 ^ 9 := colsAct_lt (by decide) _
    have hemb : emb (lamZ τ) = colsAct [1, 2, 12, 48] (lamC τ) ^^^ τ := by
      calc emb (lamZ τ) = colsAct [1, 2, 12, 48] (lamC τ) ^^^
            (colsAct [1, 2, 12, 48] (lamC τ) ^^^ emb (lamZ τ)) := by
            rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
        _ = colsAct [1, 2, 12, 48] (lamC τ) ^^^ τ := by rw [heq]
    rw [hemb, hBlin κ hκ10 _ hlt1 _ (hY9 τ hτ), hL κ hκ, hYW τ hτ κ hκ]
  have hinj : Set.InjOn f ↑Y := by
    intro τ hτ τ' hτ' h
    have e1 := (hspan τ (h512 τ hτ)).2.2
    have e2 := (hspan τ' (h512 τ' hτ')).2.2
    have h1 : lamC τ = lamC τ' := congrArg Prod.fst h
    have h2 : lamZ τ = lamZ τ' := congrArg Prod.snd h
    rw [← e1, ← e2, h1, h2]
  calc Y.card ≤ (Finset.range 16 ×ˢ fixC BT W).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = 16 * (fixC BT W).card := by rw [Finset.card_product, Finset.card_range]

theorem card_le_pc {W : Finset ℕ} {X : ℕ} (h : ∀ κ ∈ W, X.testBit κ = true)
    (hW : ∀ κ ∈ W, κ < 1024) : W.card ≤ pc X := by
  rw [pc_eq_card]
  exact Finset.card_le_card fun κ hκ => Finset.mem_filter.2 ⟨Finset.mem_range.2 (hW κ hκ), h κ hκ⟩

theorem foldl_land_le (g : Nat × Nat → ℕ) :
    ∀ (labs : List (Nat × Nat)) (m : ℕ), labs.foldl (fun m l => Nat.land m (g l)) m ≤ m
  | [], m => le_refl m
  | l :: labs, m => le_trans (foldl_land_le g labs _) Nat.and_le_left

set_option exponentiation.threshold 1024 in
theorem fixOf_lt (FA : ℕ) (labs : List (Nat × Nat)) : fixOf FA labs < 2 ^ 1024 :=
  lt_of_le_of_lt (foldl_land_le _ labs m1024) (Nat.sub_lt (Nat.two_pow_pos 1024) Nat.one_pos)

theorem phiW_eq_zero {W : Finset ℕ} : ∀ g : List ℕ, (∀ x ∈ g, x ∈ W) → phiW W g = 0
  | [], _ => rfl
  | x :: g, h => by
    rw [phiW, if_pos (h x List.mem_cons_self),
      phiW_eq_zero g (fun y hy => h y (List.mem_cons_of_mem _ hy))]

set_option exponentiation.threshold 1024 in
theorem visit_bound {C : Ctx} {RT FA FB YE NY : ℕ} {YC : List (List ℕ)} {YG : List (List YEnt)}
    {dat : Data} {r : ℕ} {row : VRow}
    (hA : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct C.AT κ x = actK dat.aCols κ x)
    (hB : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, bAct C.BT κ x = actK dat.uConjT κ x)
    (hAc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16,
      actK dat.aCols (κ ^^^ μ) x = actK dat.aCols κ (actK dat.aCols μ x))
    (hBc : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 9,
      actK dat.uConjT (κ ^^^ μ) x = actK dat.uConjT κ (actK dat.uConjT μ x))
    (hAlt : ∀ κ, ∀ x < 2 ^ 16, actK dat.aCols κ x < 2 ^ 16)
    (hβ : ∀ x < 2 ^ 16, ∀ y < 2 ^ 16, bet C.BC x y = betaN dat.beta x y)
    (hFC : ∀ i, fld C.FC (16 * i) 65535 = fval dat (fld C.FK (32 * i) m32))
    (hfa : ∀ o < 68, faOK FA C.AT RT o = true) (hfb : ∀ z < 32, fbOK FB C.BT z = true)
    (hyc : ycOK YE NY YC = true) (hyg : ygOK YE FB NY YG = true) (hNY : 0 < NY)
    (hlamB : lamBOK C.BT = true) (hlamS : lamSpan = true)
    (hvis : visitOK C RT FA YG r row = true) (hglen : ∀ c ∈ row.2, c.1.length ≤ 16)
    (hDc : (spanF (sbasis (slot RT r))).card = 2 ^ Nat.shiftRight (slot RT r) 80)
    {W Y : Finset ℕ} (hW : XorClosed W) (hW10 : ∀ κ ∈ W, κ < 2 ^ 10)
    (hWD : ∀ κ ∈ W, ∀ b ∈ sbasis (slot RT r), actK dat.aCols κ b = b)
    (hY9 : ∀ τ ∈ Y, τ < 2 ^ 9) (hYW : ∀ τ ∈ Y, ∀ κ ∈ W, actK dat.uConjT κ τ = τ)
    (hsol : ∀ ks : List ℕ, (∀ κ ∈ ks, κ ∈ W) → ∃ X, LiftPm dat (sbasis (slot RT r)) ks X) :
    (spanF (sbasis (slot RT r))).card * W.card * Y.card ≤ 2 ^ 14 := by
  classical
  obtain ⟨hlabs, hgrp⟩ := visitOK_sound hvis
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.shiftRight (slot RT r) 80 := ⟨_, rfl⟩
  rw [← hd] at hgrp hDc
  have hbs16 : ∀ b ∈ sbasis (slot RT r), b < 2 ^ 16 := by
    intro b hb
    rw [sbasis, List.mem_map] at hb
    obtain ⟨k, -, rfl⟩ := hb
    exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
  have h1024 : ∀ κ < 2 ^ 10, κ < 1024 := fun κ hκ => lt_of_lt_of_eq hκ (by norm_num)
  have hA0' : ∀ x < 2 ^ 16, aAct C.AT 0 x = x := fun x hx => by
    rw [hA 0 (Nat.two_pow_pos 10) x hx, actK_zero_left]
  have hlt' : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 16, aAct C.AT κ x < 2 ^ 16 := fun κ hκ x hx => by
    rw [hA κ hκ x hx]
    exact hAlt κ x hx
  have hc' : ∀ κ < 2 ^ 10, ∀ μ < 2 ^ 10, ∀ x < 2 ^ 16,
      aAct C.AT κ (aAct C.AT μ x) = aAct C.AT (κ ^^^ μ) x := by
    intro κ hκ μ hμ x hx
    rw [hA μ hμ x hx, hA κ hκ _ (hAlt μ x hx), hA _ (Nat.xor_lt_two_pow hκ hμ) x hx,
      hAc κ hκ μ hμ x hx]
  have hM := testBit_fixOf_fix hfa hlabs hA0' hc' hlt'
  have hB0 : ∀ κ < 2 ^ 10, bAct C.BT κ 0 = 0 := fun κ hκ => by
    rw [hB κ hκ 0 (Nat.two_pow_pos 9), actK_zero]
  have hBlin : ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, ∀ y < 2 ^ 9,
      bAct C.BT κ (x ^^^ y) = bAct C.BT κ x ^^^ bAct C.BT κ y := by
    intro κ hκ x hx y hy
    rw [hB κ hκ _ (Nat.xor_lt_two_pow hx hy), hB κ hκ x hx, hB κ hκ y hy, actK_xor]
  have hYW' : ∀ τ ∈ Y, ∀ κ ∈ W, bAct C.BT κ τ = τ := fun τ hτ κ hκ => by
    rw [hB κ (hW10 κ hκ) τ (hY9 τ hτ)]
    exact hYW τ hτ κ hκ
  have hYle := Y_card_le' hlamB hlamS hB0 hBlin hW10 hY9 hYW'
  have hC'32 : ∀ z ∈ fixC C.BT W, z < 32 := fun z hz =>
    Finset.mem_range.1 (Finset.mem_filter.1 hz).1
  have h32 : ∀ z, z < 32 → z < 2 ^ 5 := fun z hz => lt_of_lt_of_eq hz (by norm_num)
  have hC'xor : XorClosed (fixC C.BT W) := by
    refine ⟨Finset.mem_filter.2 ⟨by simp, fun κ hκ => by rw [emb_zero', hB0 κ (hW10 κ hκ)]⟩, ?_⟩
    intro z hz z' hz'
    obtain ⟨hz32, hzf⟩ := Finset.mem_filter.1 hz
    obtain ⟨hz'32, hz'f⟩ := Finset.mem_filter.1 hz'
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, fun κ hκ => ?_⟩
    · exact lt_of_lt_of_eq (Nat.xor_lt_two_pow (h32 z (Finset.mem_range.1 hz32))
        (h32 z' (Finset.mem_range.1 hz'32))) (by norm_num)
    · rw [emb_xor', hBlin κ (hW10 κ hκ) _ (emb_lt' z) _ (emb_lt' z'), hzf κ hκ, hz'f κ hκ]
  obtain ⟨i, hi, hiC⟩ := ycOK_cover hyc hNY hC'xor hC'32
  obtain ⟨hYGlen, hYGent, hYGcov⟩ := ygOK_spec hyg
  obtain ⟨s, hs, e, he, hei⟩ := hYGcov i hi
  obtain ⟨-, hpcE, hcu, hcnt⟩ := hYGent s hs e he
  rw [hei] at hpcE hcu
  have hset : fixC C.BT W =
      (Finset.range 1024).filter (fun j => (fld YE (32 * i) m32).testBit j = true) := by
    ext z
    rw [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hz
      exact ⟨lt_of_lt_of_le (hC'32 z hz) (by norm_num), (hiC z (hC'32 z hz)).2 hz⟩
    · rintro ⟨-, hbit⟩
      by_cases hz32 : z < 32
      · exact (hiC z hz32).1 hbit
      · exfalso
        have hlt : fld YE (32 * i) m32 < 2 ^ 32 :=
          lt_of_le_of_lt Nat.and_le_right (by norm_num [m32])
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt
          (Nat.pow_le_pow_right (by norm_num) (by omega)))] at hbit
        exact Bool.false_ne_true hbit
  have hC'card : (fixC C.BT W).card = 2 ^ s := by
    rw [← hpcE, pc_eq_card, hset]
  have hW1024 : ∀ κ ∈ W, κ < 1024 := fun κ hκ => h1024 κ (hW10 κ hκ)
  have hWM : ∀ κ ∈ W, (fixOf FA row.1).testBit κ = true := fun κ hκ =>
    (hM κ).2 ⟨hW1024 κ hκ, fun b hb => by
      rw [hA κ (hW10 κ hκ) b (hbs16 b hb)]
      exact hWD κ hκ b hb⟩
  have hWcu : ∀ κ ∈ W, e.2.1.testBit κ = true := fun κ hκ => by
    rw [hcu, testBit_cuOf_fix hfb]
    exact ⟨hW1024 κ hκ, fun z hz hbit => (Finset.mem_filter.1 ((hiC z hz).1 hbit)).2 κ hκ⟩
  have hWM' : ∀ κ ∈ W, (Nat.land (fixOf FA row.1) e.2.1).testBit κ = true := fun κ hκ => by
    change ((fixOf FA row.1) &&& e.2.1).testBit κ = true
    rw [Nat.testBit_and, hWM κ hκ, hWcu κ hκ]
    rfl
  have c1 := card_le_pc hWM hW1024
  have c2 : W.card ≤ e.2.2 := by
    rw [hcnt]
    exact card_le_pc hWcu hW1024
  have c3 := card_le_pc hWM' hW1024
  have hsum : (spanF (sbasis (slot RT r))).card * W.card * Y.card ≤ 2 ^ (d + 4 + s) * W.card := by
    rw [hDc, pow_add, pow_add, ← hC'card]
    calc 2 ^ d * W.card * Y.card ≤ 2 ^ d * W.card * (16 * (fixC C.BT W).card) :=
          Nat.mul_le_mul_left _ hYle
      _ = 2 ^ d * 2 ^ 4 * (fixC C.BT W).card * W.card := by ring
  by_contra hcon
  have hgt : 16384 < 2 ^ (d + 4 + s) * W.card := by
    have := lt_of_lt_of_le (not_le.1 hcon) hsum
    norm_num at this
    exact this
  have h0 : 16384 < 2 ^ (d + 4 + s) * pc (fixOf FA row.1) :=
    lt_of_lt_of_le hgt (Nat.mul_le_mul_left _ c1)
  have h1 : 16384 < 2 ^ (d + 4 + s) * e.2.2 := lt_of_lt_of_le hgt (Nat.mul_le_mul_left _ c2)
  have h2 : 16384 < 2 ^ (d + 4 + s) * pc (Nat.land (fixOf FA row.1) e.2.1) :=
    lt_of_lt_of_le hgt (Nat.mul_le_mul_left _ c3)
  obtain ⟨c, hcrow, hcand⟩ := hgrp s (by rw [hYGlen]; exact hs) e he h0 h1 h2
  have hM'lt : Nat.land (fixOf FA row.1) e.2.1 < 2 ^ 1024 :=
    lt_of_le_of_lt Nat.and_le_left (fixOf_lt FA row.1)
  obtain ⟨hg, ha, hφ⟩ := cand_noSol hA hB hβ hFC hbs16 hM'lt hcand
  set M' := Nat.land (fixOf FA row.1) e.2.1 with hM'def
  set S := (Finset.range 1024).filter fun κ => M'.testBit κ = true with hSdef
  have hmemS : ∀ κ, κ ∈ S ↔ κ < 1024 ∧ M'.testBit κ = true := fun κ => by
    rw [hSdef, Finset.mem_filter, Finset.mem_range]
  have hbitM' : ∀ κ, M'.testBit κ = true ↔
      (κ < 1024 ∧ ∀ b ∈ sbasis (slot RT r), aAct C.AT κ b = b) ∧
        (κ < 1024 ∧ ∀ z < 32, (fld YE (32 * i) m32).testBit z = true →
          bAct C.BT κ (emb z) = emb z) := fun κ => by
    change ((fixOf FA row.1) &&& e.2.1).testBit κ = true ↔ _
    rw [Nat.testBit_and, Bool.and_eq_true, hM κ, hcu, testBit_cuOf_fix hfb]
  have hSxor : XorClosed S := by
    refine ⟨(hmemS 0).2 ⟨by norm_num, (hbitM' 0).2 ⟨⟨by norm_num, fun b hb => hA0' b (hbs16 b hb)⟩,
      ⟨by norm_num, fun z _ _ => by rw [hB 0 (Nat.two_pow_pos 10) _ (emb_lt' z),
        actK_zero_left]⟩⟩⟩, ?_⟩
    intro κ hκ μ hμ
    obtain ⟨hκ1, hκb⟩ := (hmemS κ).1 hκ
    obtain ⟨hμ1, hμb⟩ := (hmemS μ).1 hμ
    obtain ⟨⟨-, hκA⟩, ⟨-, hκB⟩⟩ := (hbitM' κ).1 hκb
    obtain ⟨⟨-, hμA⟩, ⟨-, hμB⟩⟩ := (hbitM' μ).1 hμb
    have hκ10 : κ < 2 ^ 10 := lt_of_lt_of_eq hκ1 (by norm_num)
    have hμ10 : μ < 2 ^ 10 := lt_of_lt_of_eq hμ1 (by norm_num)
    have hx10 := Nat.xor_lt_two_pow hκ10 hμ10
    refine (hmemS _).2 ⟨h1024 _ hx10, (hbitM' _).2 ⟨⟨h1024 _ hx10, fun b hb => ?_⟩,
      ⟨h1024 _ hx10, fun z hz hbit => ?_⟩⟩⟩
    · rw [← hc' κ hκ10 μ hμ10 b (hbs16 b hb), hμA b hb, hκA b hb]
    · rw [hB _ hx10 _ (emb_lt' z), hBc κ hκ10 μ hμ10 _ (emb_lt' z), ← hB μ hμ10 _ (emb_lt' z),
        hμB z hz hbit, ← hB κ hκ10 _ (emb_lt' z), hκB z hz hbit]
  have hWS : W ⊆ S := fun κ hκ => (hmemS κ).2 ⟨hW1024 κ hκ, hWM' κ hκ⟩
  have hgS : ∀ x ∈ c.1, x ∈ S := by
    intro x hx
    refine (hmemS x).2 ⟨?_, hg x hx⟩
    by_contra hge
    have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hM'lt
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hge)))
    rw [hg x hx] at this
    exact Bool.noConfusion this
  have hScard : S.card = pc M' := (pc_eq_card M').symm
  have hpos : 0 < 2 ^ (d + 4 + s) := Nat.two_pow_pos _
  have h4 : S.card < 4 * W.card := by
    rw [hScard]
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (d + 4 + s)) ?_
    calc 2 ^ (d + 4 + s) * pc M' ≤ 65536 := ha
      _ < 4 * 16384 + 1 := by norm_num
      _ ≤ 2 ^ (d + 4 + s) * (4 * W.card) := by nlinarith
  have hidx := idxTwo_of_card hSxor hW hWS h4
  have hφlt : phiW W c.1 < (if 2 ^ (d + 4 + s) * pc M' ≤ 32768 then 1 else 2 ^ c.1.length) := by
    split_ifs with h15
    · have h2W : S.card < 2 * W.card := by
        rw [hScard]
        refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (d + 4 + s)) ?_
        calc 2 ^ (d + 4 + s) * pc M' ≤ 32768 := h15
          _ < 2 * 16384 + 1 := by norm_num
          _ ≤ 2 ^ (d + 4 + s) * (2 * W.card) := by nlinarith
      have hWeq := eq_of_card_lt_two_mul hW hSxor hWS h2W
      rw [phiW_eq_zero c.1 (fun x hx => hWeq ▸ hgS x hx)]
      exact Nat.one_pos
    · exact phiW_lt W c.1
  obtain ⟨cs, hcs, hno⟩ := hφ _ hφlt
  obtain ⟨X, hX⟩ := hsol (cs.map (lAct c.1)) (fun κ hκ => by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hκ
    exact lAct_mem_of_par16 hSxor hW hidx hgS (hglen c hcrow) (hcs x hx))
  exact hno X hX

end CFSG.KC.P0Vis

end
