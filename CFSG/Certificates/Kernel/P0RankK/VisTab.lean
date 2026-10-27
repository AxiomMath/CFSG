module

public import CFSG.Monster.B.TwoA.Sp8.P0RankLin
public import Certificates.Data.Kernel.P0Vis
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.Bound.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Vis

open CFSG.KC.P0Orb CFSG.Monster.B.TwoA.Sp8.P0Rank MonsterB.P0Rank

@[expose] def fields (w m p : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => (p &&& m) :: fields w m (p >>> w) n

theorem pAct_succ (w m n p x : ℕ) : pAct w m (n + 1) p x =
    bif Nat.beq x 0 then 0 else Nat.xor (bif Nat.beq (Nat.land x 1) 1 then Nat.land p m else 0)
      (pAct w m n (Nat.shiftRight p w) (Nat.shiftRight x 1)) := rfl

theorem pAct_eq_colsAct (w m : ℕ) : ∀ n p x, x < 2 ^ n → pAct w m n p x = colsAct (fields w m p n) x
  | 0, p, x, hx => by
    have : x = 0 := by simpa using hx
    subst this
    rfl
  | n + 1, p, x, hx => by
    rw [pAct_succ, fields, colsAct]
    by_cases hx0 : x = 0
    · subst hx0
      simp [colsAct_zero]
    · have hb : Nat.beq x 0 = false := by
        cases h : Nat.beq x 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hx0
      have e1 : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x
      have e2 : Nat.shiftRight x 1 = x / 2 := by
        change x >>> 1 = x / 2
        rw [Nat.shiftRight_eq_div_pow, pow_one]
      have hlt : x / 2 < 2 ^ n := by
        rw [pow_succ] at hx
        omega
      rw [hb, e1, e2, cond_false]
      change (bif Nat.beq (x % 2) 1 then p &&& m else 0) ^^^ pAct w m n (p >>> w) (x / 2) = _
      rw [pAct_eq_colsAct w m n _ _ hlt]
      rcases Nat.mod_two_eq_zero_or_one x with h | h
      · rw [h]
        rfl
      · rw [h]
        rfl

theorem length_fields (w m p : ℕ) : ∀ n, (fields w m p n).length = n
  | 0 => rfl
  | n + 1 => by simp [fields, length_fields w m _ n]

theorem pAct_lt {w : ℕ} : ∀ n p x, pAct w (2 ^ w - 1) n p x < 2 ^ w
  | 0, _, _ => Nat.two_pow_pos w
  | n + 1, p, x => by
    rw [pAct_succ]
    cases Nat.beq x 0
    · refine Nat.xor_lt_two_pow ?_ (pAct_lt n _ _)
      cases Nat.beq (Nat.land x 1) 1
      · exact Nat.two_pow_pos w
      · change p &&& (2 ^ w - 1) < 2 ^ w
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact Nat.two_pow_pos w

theorem colsAct_map {g : ℕ → ℕ} (hg0 : g 0 = 0) (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) :
    ∀ (cs : List ℕ) (x : ℕ), colsAct (cs.map g) x = g (colsAct cs x)
  | [], _ => by simp [colsAct, hg0]
  | c :: cs, x => by
    rw [List.map_cons, colsAct, colsAct, colsAct_map hg0 hg cs, hg]
    split_ifs <;> simp [hg0]

theorem rowB_cons (p x : ℕ) (xs : List ℕ) :
    rowB p (x :: xs) = pAct 9 511 9 p x ||| rowB p xs <<< 9 := rfl

theorem or_shl_eq {a r : ℕ} (ha : a < 2 ^ 9) : a ||| r <<< 9 = a + 2 ^ 9 * r := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha r, Nat.shiftLeft_eq, Nat.mul_comm,
    Nat.add_comm]

theorem fields_rowB (p : ℕ) : ∀ xs : List ℕ,
    fields 9 511 (rowB p xs) xs.length = xs.map (pAct 9 511 9 p)
  | [] => rfl
  | x :: xs => by
    have ha : pAct 9 511 9 p x < 2 ^ 9 := pAct_lt (w := 9) 9 p x
    rw [List.length_cons, fields, rowB_cons, or_shl_eq ha, List.map_cons]
    congr 1
    · change (pAct 9 511 9 p x + 2 ^ 9 * rowB p xs) &&& (2 ^ 9 - 1) = _
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    · rw [Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos 9),
        Nat.div_eq_of_lt ha, Nat.zero_add]
      exact fields_rowB p xs

@[expose] def actF (cols : List (List ℕ)) (κ : ℕ) (n x : ℕ) : ℕ :=
  (List.range n).foldr (fun k y => if κ.testBit k then colsAct (cols.getD k []) y else y) x

theorem actF_succ (cols : List (List ℕ)) (κ n x : ℕ) :
    actF cols κ (n + 1) x =
      actF cols κ n (if κ.testBit n then colsAct (cols.getD n []) x else x) := by
  rw [actF, List.range_succ, List.foldr_append]
  rfl

theorem actF_stable (cols : List (List ℕ)) (κ t : ℕ) (x : ℕ) :
    ∀ n, t ≤ n → (∀ k, t ≤ k → k < n → κ.testBit k = false) → actF cols κ n x = actF cols κ t x
  | 0, h, _ => by rw [Nat.le_zero.1 h]
  | n + 1, h, hb => by
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · rfl
    · rw [actF_succ, hb n (by omega) (by omega), if_neg (by simp),
        actF_stable cols κ t x n (by omega) (fun k h1 h2 => hb k h1 (by omega))]

theorem actF_congr (cols : List (List ℕ)) (κ κ' : ℕ) :
    ∀ t, (∀ k < t, κ.testBit k = κ'.testBit k) → ∀ x, actF cols κ t x = actF cols κ' t x
  | 0, _, _ => rfl
  | t + 1, h, x => by
    rw [actF_succ, actF_succ, h t (by omega),
      actF_congr cols κ κ' t (fun k hk => h k (by omega))]

theorem actK_add_two_pow (cols : List (List ℕ)) {κ t : ℕ} (hκ : κ < 2 ^ t)
    (ht : t < cols.length) (x : ℕ) :
    actK cols (κ + 2 ^ t) x = actK cols κ (colsAct (cols.getD t []) x) := by
  have hlt : κ + 2 ^ t < 2 ^ (t + 1) := by rw [pow_succ]; omega
  have hbit_hi : ∀ k, t + 1 ≤ k → (κ + 2 ^ t).testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk))
  have hbit_t : (κ + 2 ^ t).testBit t = true := by
    rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hκ]
    rfl
  have hbit_lo : ∀ k < t, (κ + 2 ^ t).testBit k = κ.testBit k := fun k hk => by
    rw [Nat.add_comm]
    exact Nat.testBit_two_pow_add_gt hk κ
  change actF cols (κ + 2 ^ t) cols.length x = actF cols κ cols.length _
  rw [actF_stable cols (κ + 2 ^ t) (t + 1) x cols.length ht (fun k h1 _ => hbit_hi k h1),
    actF_succ, hbit_t, if_pos rfl,
    actF_stable cols κ t _ cols.length ht.le (fun k h1 _ =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hκ (Nat.pow_le_pow_right (by norm_num) h1)))]
  exact actF_congr cols _ _ t hbit_lo _

private theorem id_fields : fields 9 511 ((List.range 9).foldl (fun a j => a ||| 2 ^ (10 * j)) 0) 9 =
    [1, 2, 4, 8, 16, 32, 64, 128, 256] := by decide +kernel

private theorem colsAct_id : ∀ x < 2 ^ 9, colsAct [1, 2, 4, 8, 16, 32, 64, 128, 256] x = x := by
  decide +kernel

theorem bAct_eq (BT κ : ℕ) {x : ℕ} (hx : x < 2 ^ 9) :
    bAct BT κ x = colsAct (fields 9 511 (fld BT (96 * κ) m96) 9) x :=
  pAct_eq_colsAct 9 511 9 _ x hx

theorem bAct_eq_actK {BT : ℕ} {BG : List (List ℕ)} (h0 : bt0OK BT BG = true)
    (hrows : ∀ t < 10, btOK BT BG t = true) (hBG : ∀ cs ∈ BG, ∀ c ∈ cs, c < 2 ^ 9) :
    ∀ κ < 2 ^ 10, ∀ x < 2 ^ 9, bAct BT κ x = actK BG κ x := by
  rw [bt0OK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h0
  have hid := Nat.eq_of_beq_eq_true h0.1.1.1
  have hlen : BG.length = 10 := Nat.eq_of_beq_eq_true h0.1.1.2
  have hcols : ∀ cs ∈ BG, cs.length = 9 := fun cs hcs =>
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h0.1.2 cs hcs)
  have key : ∀ t ≤ 10, ∀ κ < 2 ^ t, ∀ x < 2 ^ 9, bAct BT κ x = actK BG κ x := by
    intro t
    induction t with
    | zero =>
      intro _ κ hκ x hx
      have : κ = 0 := by simpa using hκ
      subst this
      rw [bAct_eq _ _ hx, Nat.mul_zero, hid, id_fields, colsAct_id x hx, actK_zero_left]
    | succ t ih =>
      intro ht κ hκ x hx
      by_cases hlo : κ < 2 ^ t
      · exact ih (by omega) κ hlo x hx
      obtain ⟨κ', rfl⟩ : ∃ κ', κ = κ' + 2 ^ t := ⟨κ - 2 ^ t, by omega⟩
      have hκ' : κ' < 2 ^ t := by rw [pow_succ] at hκ; omega
      have hrow := hrows t (by omega)
      simp only [btOK, List.all_eq_true, List.mem_range, Nat.beq_eq] at hrow
      have hr := hrow κ' hκ'
      have hBGt : BG.getD t [] ∈ BG := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have hlen9 : (BG.getD t []).length = 9 := by
        have := hcols _ hBGt
        simpa using this
      have hcs := hBG _ hBGt
      have hcol_lt : colsAct (BG.getD t []) x < 2 ^ 9 := colsAct_lt hcs x
      have hf := fields_rowB (fld BT (96 * κ') m96) (BG.getD t [])
      rw [hlen9] at hf
      rw [bAct_eq _ _ hx, hr, hf]
      let g := colsAct (fields 9 511 (fld BT (96 * κ') m96) 9)
      have hmap : (BG.getD t []).map (pAct 9 511 9 (fld BT (96 * κ') m96)) =
          (BG.getD t []).map g :=
        List.map_congr_left fun c hc => pAct_eq_colsAct 9 511 9 _ c (hcs c hc)
      rw [hmap, colsAct_map (colsAct_zero _) (colsAct_xor _), ← bAct_eq _ _ hcol_lt,
        ih (by omega) κ' hκ' _ hcol_lt, actK_add_two_pow BG hκ' (by omega)]
  exact key 10 le_rfl

end CFSG.KC.P0Vis

end
