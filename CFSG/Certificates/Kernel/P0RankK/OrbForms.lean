module

public import CFSG.Certificates.Kernel.P0RankK.VisFark
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.P0Orb

open MonsterB.P0Rank CFSG.Monster.B.TwoA.Sp8.P0Rank

theorem ite_xor_bool (a b : Bool) (c : ℕ) :
    (if (a ^^ b) = true then c else 0) = (if a = true then c else 0) ^^^ (if b = true then c else 0) := by
  cases a <;> cases b <;> simp

def p0bXS (n : ℕ) (f : ℕ → ℕ) : ℕ := (List.range n).foldr (fun k a => f k ^^^ a) 0

theorem p0bXS_foldr (f : ℕ → ℕ) : ∀ (l : List ℕ) (s : ℕ),
    l.foldr (fun k a => f k ^^^ a) s = l.foldr (fun k a => f k ^^^ a) 0 ^^^ s
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldr_cons, List.foldr_cons, p0bXS_foldr f l s, Nat.xor_assoc]

theorem p0bXS_succ (n : ℕ) (f : ℕ → ℕ) : p0bXS (n + 1) f = p0bXS n f ^^^ f n := by
  unfold p0bXS
  rw [List.range_succ, List.foldr_append, p0bXS_foldr]
  simp

theorem p0bXS_succ' (f : ℕ → ℕ) : ∀ n, p0bXS (n + 1) f = f 0 ^^^ p0bXS n (fun k => f (k + 1))
  | 0 => by simp [p0bXS]
  | n + 1 => by
    rw [p0bXS_succ, p0bXS_succ' f n, p0bXS_succ, Nat.xor_assoc]

theorem p0bXS_congr {f g : ℕ → ℕ} : ∀ {n : ℕ}, (∀ k < n, f k = g k) → p0bXS n f = p0bXS n g
  | 0, _ => rfl
  | n + 1, h => by
    rw [p0bXS_succ, p0bXS_succ, p0bXS_congr fun k hk => h k (by omega), h n (by omega)]

theorem p0bXS_zero_fun (n : ℕ) : p0bXS n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [p0bXS_succ, ih, Nat.zero_xor]

theorem p0bXS_xor (f g : ℕ → ℕ) (n : ℕ) :
    p0bXS n (fun k => f k ^^^ g k) = p0bXS n f ^^^ p0bXS n g := by
  induction n with
  | zero => simp [p0bXS]
  | succ n ih =>
    rw [p0bXS_succ, p0bXS_succ, p0bXS_succ, ih]
    ac_rfl

theorem p0bXS_ite (c : Prop) [Decidable c] (n : ℕ) (f : ℕ → ℕ) :
    (if c then p0bXS n f else 0) = p0bXS n (fun k => if c then f k else 0) := by
  split_ifs
  · rfl
  · exact (p0bXS_zero_fun n).symm

theorem p0bXS_swap (g : ℕ → ℕ → ℕ) (m : ℕ) : ∀ n,
    p0bXS n (fun i => p0bXS m (g i)) = p0bXS m (fun j => p0bXS n (fun i => g i j))
  | 0 => (p0bXS_zero_fun m).symm
  | n + 1 => by
    rw [p0bXS_succ, p0bXS_swap g m n, ← p0bXS_xor]
    exact p0bXS_congr fun j _ => (p0bXS_succ n _).symm

theorem p0bXS_lt (f : ℕ → ℕ) {j : ℕ} : ∀ n, j ≤ n →
    p0bXS n (fun i => if i < j then f i else 0) = p0bXS j f
  | 0, hj => by
    have : j = 0 := by omega
    subst this
    rfl
  | n + 1, hj => by
    by_cases h : j ≤ n
    · rw [p0bXS_succ, p0bXS_lt f n h, if_neg (by omega), Nat.xor_zero]
    · have : j = n + 1 := by omega
      subst this
      exact p0bXS_congr fun k hk => if_pos hk

theorem p0b_colsAct_eq : ∀ (cs : List ℕ) (x : ℕ),
    colsAct cs x = p0bXS cs.length (fun k => if x.testBit k then cs.getD k 0 else 0)
  | [], _ => rfl
  | c :: cs, x => by
    rw [colsAct.eq_2, p0b_colsAct_eq cs (x / 2), List.length_cons, p0bXS_succ']
    congr 1
    · rw [Nat.testBit_zero]
      by_cases hx : x % 2 = 1 <;> simp [hx]
    · exact p0bXS_congr fun k _ => by rw [Nat.testBit_div_two, List.getD_cons_succ]

theorem p0b_foldl (b : ℕ → Bool) (v : ℕ → ℕ) : ∀ n,
    (List.range n).foldl (fun acc j => if b j then acc ^^^ v j else acc) 0 =
      p0bXS n (fun j => if b j then v j else 0)
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, p0b_foldl b v n, p0bXS_succ, List.foldl_cons,
      List.foldl_nil]
    cases b n <;> simp

theorem p0b_fields_eq (w m : ℕ) : ∀ n p,
    CFSG.KC.P0Vis.fields w m p n = (List.range n).map fun i => (p >>> (w * i)) &&& m
  | 0, _ => rfl
  | n + 1, p => by
    simp only [CFSG.KC.P0Vis.fields]
    rw [p0b_fields_eq w m n, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    change p >>> w >>> (w * i) &&& m = p >>> (w * (i + 1)) &&& m
    rw [← Nat.shiftRight_add, Nat.mul_add_one, Nat.add_comm (w * i) w]

theorem p0b_g_lin (s m : ℕ) (a b : ℕ) :
    ((a ^^^ b) >>> s) &&& m = ((a >>> s) &&& m) ^^^ ((b >>> s) &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases a.testBit (s + k) <;> cases b.testBit (s + k) <;> cases m.testBit k <;> rfl

theorem p0b_fld2 (P i j : ℕ) (hi : i < 16) :
    (((P >>> (144 * j)) &&& m144) >>> (9 * i)) &&& 511 = fld P (144 * j + 9 * i) 511 := by
  have hm : m144 = 2 ^ 144 - 1 := rfl
  have h511 : (511 : ℕ) = 2 ^ 9 - 1 := rfl
  change _ = (P >>> (144 * j + 9 * i)) &&& 511
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, hm, h511, Nat.testBit_two_pow_sub_one]
  by_cases hk : k < 9
  · have hk' : 9 * i + k < 144 := by omega
    simp [hk, hk', Nat.add_assoc]
  · simp [hk]

theorem p0b_pp (P x y : ℕ) (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) :
    pAct 9 511 16 (pAct 144 m144 16 P y) x = colsAct ((List.range 16).map fun i =>
      colsAct ((List.range 16).map fun j => fld P (144 * j + 9 * i) 511) y) x := by
  rw [CFSG.KC.P0Vis.pAct_eq_colsAct _ _ 16 _ x hx, CFSG.KC.P0Vis.pAct_eq_colsAct _ _ 16 _ y hy,
    p0b_fields_eq, p0b_fields_eq]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  rw [← CFSG.KC.P0Vis.colsAct_map (g := fun p => (p >>> (9 * i)) &&& 511) (by simp)
    (p0b_g_lin _ _), List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => p0b_fld2 P i j hi'

theorem p0b_bc_facts {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) :
    (∀ i < 16, (beta.getD i []).length = 16) ∧
    (∀ i < 16, ∀ j < 16, fld BC (144 * j + 9 * i) 511 = (beta.getD i []).getD j 0) ∧
    ∀ i < 16, ∀ j < 16, fld BU (144 * j + 9 * i) 511 =
      if i < j then (beta.getD j []).getD i 0 else 0 := by
  unfold bcOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨hlen, hrows⟩, hmain⟩, _⟩, _⟩, _⟩ := h
  refine ⟨fun i hi => ?_, fun i hi j hj => (hmain i hi j hj).1.2, fun i hi j hj => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega)]
    exact hrows _ (List.getElem_mem _)
  · rw [(hmain i hi j hj).2]
    cases hb : Nat.blt i j
    · have hn : ¬ i < j := fun h' => by
        have h2 : Nat.blt i j = true := by
          rw [Nat.blt_eq]
          exact h'
        rw [hb] at h2
        exact Bool.noConfusion h2
      rw [if_neg hn]
      rfl
    · have hp : i < j := by
        rw [← Nat.blt_eq]
        exact hb
      rw [if_pos hp]
      rfl

def p0oB (f : ℕ → ℕ → ℕ) (x y : ℕ) : ℕ :=
  p0bXS 16 fun i => p0bXS 16 fun j => if x.testBit i then if y.testBit j then f i j else 0 else 0

theorem p0oB_xor_left (f : ℕ → ℕ → ℕ) (x x' y : ℕ) :
    p0oB f (x ^^^ x') y = p0oB f x y ^^^ p0oB f x' y := by
  unfold p0oB
  rw [← p0bXS_xor]
  refine p0bXS_congr fun i _ => ?_
  rw [← p0bXS_xor]
  refine p0bXS_congr fun j _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit i <;> cases x'.testBit i <;> simp

theorem p0oB_xor_right (f : ℕ → ℕ → ℕ) (x y y' : ℕ) :
    p0oB f x (y ^^^ y') = p0oB f x y ^^^ p0oB f x y' := by
  unfold p0oB
  rw [← p0bXS_xor]
  refine p0bXS_congr fun i _ => ?_
  rw [← p0bXS_xor]
  refine p0bXS_congr fun j _ => ?_
  rw [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit j <;> cases y'.testBit j <;> simp

theorem p0oB_swap (f : ℕ → ℕ → ℕ) (x y : ℕ) : p0oB f x y = p0oB (fun i j => f j i) y x := by
  unfold p0oB
  rw [p0bXS_swap]
  refine p0bXS_congr fun j _ => p0bXS_congr fun i _ => ?_
  cases x.testBit i <;> cases y.testBit j <;> simp

theorem p0oB_xor_fun (f g : ℕ → ℕ → ℕ) (x y : ℕ) :
    p0oB f x y ^^^ p0oB g x y = p0oB (fun i j => f i j ^^^ g i j) x y := by
  unfold p0oB
  rw [← p0bXS_xor]
  refine p0bXS_congr fun i _ => ?_
  rw [← p0bXS_xor]
  refine p0bXS_congr fun j _ => ?_
  cases x.testBit i <;> cases y.testBit j <;> simp

theorem p0oB_congr {f g : ℕ → ℕ → ℕ} (h : ∀ i < 16, ∀ j < 16, f i j = g i j) (x y : ℕ) :
    p0oB f x y = p0oB g x y :=
  p0bXS_congr fun i hi => p0bXS_congr fun j hj => by rw [h i hi j hj]

theorem p0o_xs_sym (g : ℕ → ℕ → ℕ) : ∀ n, (∀ i < n, ∀ j < n, g i j = g j i) →
    (∀ i < n, g i i = 0) → p0bXS n (fun i => p0bXS n (g i)) = 0
  | 0, _, _ => rfl
  | n + 1, hs, hd => by
    have ih := p0o_xs_sym g n (fun i hi j hj => hs i (by omega) j (by omega))
      (fun i hi => hd i (by omega))
    have e1 : p0bXS n (fun i => g i n) = p0bXS n (g n) :=
      p0bXS_congr fun i hi => hs i (by omega) n (by omega)
    simp only [p0bXS_succ]
    rw [p0bXS_xor, ih, e1, hd n (by omega), Nat.zero_xor, Nat.xor_zero, Nat.xor_self]

theorem p0oB_self {f : ℕ → ℕ → ℕ} (hs : ∀ i < 16, ∀ j < 16, f i j = f j i)
    (hd : ∀ i < 16, f i i = 0) (x : ℕ) : p0oB f x x = 0 := by
  unfold p0oB
  refine p0o_xs_sym _ 16 (fun i hi j hj => ?_) (fun i hi => ?_)
  · cases x.testBit i <;> cases x.testBit j <;> simp [hs i hi j hj]
  · cases x.testBit i <;> simp [hd i hi]

theorem p0o_bet_eq (BC : ℕ) {x y : ℕ} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) :
    bet BC x y = p0oB (fun i j => fld BC (144 * j + 9 * i) 511) x y := by
  rw [bet, p0b_pp BC x y hx hy, p0b_colsAct_eq, List.length_map, List.length_range]
  refine p0bXS_congr fun i hi => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range,
    p0b_colsAct_eq, List.length_map, List.length_range, p0bXS_ite]
  refine p0bXS_congr fun j hj => ?_
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

theorem p0o_qf_eq (BU : ℕ) {x : ℕ} (hx : x < 2 ^ 16) :
    qf BU x = p0oB (fun i j => fld BU (144 * j + 9 * i) 511) x x :=
  p0o_bet_eq BU hx hx

theorem p0o_bet_lt (BC x y : ℕ) : bet BC x y < 2 ^ 9 :=
  CFSG.KC.P0Vis.pAct_lt (w := 9) 16 _ x

theorem p0o_bet_zero_left (BC y : ℕ) : bet BC 0 y = 0 := CFSG.KC.P0Vis.pAct_zero_x _ _ 16 _

theorem p0o_qf_zero (BU : ℕ) : qf BU 0 = 0 := CFSG.KC.P0Vis.pAct_zero_x _ _ 16 _

theorem p0o_bet_zero_right (BC : ℕ) {x : ℕ} (hx : x < 2 ^ 16) : bet BC x 0 = 0 := by
  rw [p0o_bet_eq BC hx (Nat.two_pow_pos 16)]
  unfold p0oB
  simp [p0bXS_zero_fun]

theorem p0o_bet_xor_left (BC : ℕ) {x x' y : ℕ} (hx : x < 2 ^ 16) (hx' : x' < 2 ^ 16)
    (hy : y < 2 ^ 16) : bet BC (x ^^^ x') y = bet BC x y ^^^ bet BC x' y := by
  rw [p0o_bet_eq BC (Nat.xor_lt_two_pow hx hx') hy, p0o_bet_eq BC hx hy, p0o_bet_eq BC hx' hy,
    p0oB_xor_left]

theorem p0o_bet_xor_right (BC : ℕ) {x y y' : ℕ} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16)
    (hy' : y' < 2 ^ 16) : bet BC x (y ^^^ y') = bet BC x y ^^^ bet BC x y' := by
  rw [p0o_bet_eq BC hx (Nat.xor_lt_two_pow hy hy'), p0o_bet_eq BC hx hy, p0o_bet_eq BC hx hy',
    p0oB_xor_right]

theorem p0o_bc_facts {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) :
    (∀ i < 16, ∀ j < 16, fld BC (144 * j + 9 * i) 511 = fld BC (144 * i + 9 * j) 511) ∧
    (∀ i < 16, fld BC (144 * i + 9 * i) 511 = 0) ∧
    ∀ i < 16, ∀ j < 16, fld BU (144 * j + 9 * i) 511 ^^^ fld BU (144 * i + 9 * j) 511 =
      fld BC (144 * j + 9 * i) 511 := by
  obtain ⟨-, hC, hU⟩ := p0b_bc_facts h
  have hsd : (∀ i < 16, ∀ j < 16, (beta.getD i []).getD j 0 = (beta.getD j []).getD i 0) ∧
      ∀ i < 16, (beta.getD i []).getD i 0 = 0 := by
    unfold bcOK at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq] at h
    exact ⟨fun i hi j hj => (h.1.1.1.2 i hi j hj).1.1.1, h.1.1.2⟩
  refine ⟨fun i hi j hj => ?_, fun i hi => ?_, fun i hi j hj => ?_⟩
  · rw [hC i hi j hj, hC j hj i hi, hsd.1 i hi j hj]
  · rw [hC i hi i hi, hsd.2 i hi]
  · rw [hU i hi j hj, hU j hj i hi, hC i hi j hj]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_pos hij, if_neg (by omega), Nat.xor_zero, hsd.1 j hj i hi]
    · rw [if_neg (lt_irrefl _), Nat.xor_zero, hsd.2 i hi]
    · rw [if_neg (by omega), if_pos hij, Nat.zero_xor]

theorem p0o_bet_comm {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) {x y : ℕ}
    (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) : bet BC x y = bet BC y x := by
  rw [p0o_bet_eq BC hx hy, p0o_bet_eq BC hy hx, p0oB_swap]
  exact p0oB_congr (fun i hi j hj => (p0o_bc_facts h).1 j hj i hi) y x

theorem p0o_bet_self {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) {x : ℕ}
    (hx : x < 2 ^ 16) : bet BC x x = 0 := by
  rw [p0o_bet_eq BC hx hx]
  exact p0oB_self (p0o_bc_facts h).1 (p0o_bc_facts h).2.1 x

theorem p0o_qf_xor {BC BU : ℕ} {beta : List (List ℕ)} (h : bcOK BC BU beta = true) {x y : ℕ}
    (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) :
    qf BU (x ^^^ y) = qf BU x ^^^ qf BU y ^^^ bet BC x y := by
  rw [p0o_qf_eq BU (Nat.xor_lt_two_pow hx hy), p0o_qf_eq BU hx, p0o_qf_eq BU hy, p0oB_xor_left,
    p0oB_xor_right, p0oB_xor_right, p0oB_swap _ y x]
  have e : p0oB (fun i j => fld BU (144 * j + 9 * i) 511) x y ^^^
      p0oB (fun i j => fld BU (144 * i + 9 * j) 511) x y = bet BC x y := by
    rw [p0oB_xor_fun, p0o_bet_eq BC hx hy]
    exact p0oB_congr (fun i hi j hj => (p0o_bc_facts h).2.2 i hi j hj) x y
  rw [← e]
  ac_rfl

theorem p0o_aAct_xor (AT lam : ℕ) {x y : ℕ} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) :
    aAct AT lam (x ^^^ y) = aAct AT lam x ^^^ aAct AT lam y := by
  unfold aAct
  rw [CFSG.KC.P0Vis.pAct_eq_colsAct _ _ 16 _ _ (Nat.xor_lt_two_pow hx hy),
    CFSG.KC.P0Vis.pAct_eq_colsAct _ _ 16 _ _ hx, CFSG.KC.P0Vis.pAct_eq_colsAct _ _ 16 _ _ hy,
    colsAct_xor]

theorem p0o_aAct_zero (AT lam : ℕ) : aAct AT lam 0 = 0 := CFSG.KC.P0Vis.pAct_zero_x _ _ 16 _

end CFSG.KC.P0Orb

end
