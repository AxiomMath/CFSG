module

public import Certificates.Data.Kernel.Mat8P

public section

namespace CFSG.KC.Mat8P

open CFSG.Quasithin.H13.Mat8Cert

@[expose] def lanes : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + 2 ^ 8 * lanes n

theorem testBit_one_add (K j : ℕ) :
    (1 + 2 ^ 8 * K).testBit j = if j < 8 then decide (j = 0) else K.testBit (j - 8) := by
  rw [Nat.add_comm, Nat.testBit_two_pow_mul_add K (by norm_num)]
  split_ifs with h
  · rcases j with _ | j
    · simp
    · simp [Nat.testBit_succ]
  · rfl

theorem and_lanes_succ (Z K : ℕ) :
    Z &&& (1 + 2 ^ 8 * K) = (Z &&& 1) + 2 ^ 8 * ((Z >>> 8) &&& K) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : Z &&& 1 < 2 ^ 8 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  rw [Nat.testBit_and, testBit_one_add, Nat.add_comm (Z &&& 1),
    Nat.testBit_two_pow_mul_add _ h1]
  split_ifs with h
  · rw [Nat.testBit_and]
    rcases j with _ | j
    · simp
    · simp [Nat.testBit_succ]
  · rw [Nat.testBit_and, Nat.testBit_shiftRight]
    congr 2
    omega

theorem and_one_mul_testBit (Z c b : ℕ) (hc : c < 2 ^ 8) :
    ((Z &&& 1) * c).testBit b = (Z.testBit 0 && c.testBit b) := by
  rw [Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one Z with h | h
  · have : Z.testBit 0 = false := by simp [Nat.testBit_zero, h]
    simp [h, this]
  · have : Z.testBit 0 = true := by simp [Nat.testBit_zero, h]
    simp [h, this]

theorem lanes_mul_testBit : ∀ (n Z c : ℕ), c < 2 ^ 8 → ∀ j b, b < 8 →
    ((Z &&& lanes n) * c).testBit (8 * j + b) =
      (decide (j < n) && Z.testBit (8 * j) && c.testBit b)
  | 0, Z, c, _, j, b, _ => by simp [lanes]
  | n + 1, Z, c, hc, j, b, hb => by
    rw [lanes, and_lanes_succ, Nat.add_mul, Nat.mul_assoc]
    have h1 : (Z &&& 1) * c < 2 ^ 8 := by
      have : Z &&& 1 ≤ 1 := Nat.and_le_right
      calc (Z &&& 1) * c ≤ 1 * c := Nat.mul_le_mul_right c this
        _ < 2 ^ 8 := by omega
    rw [Nat.add_comm ((Z &&& 1) * c), Nat.testBit_two_pow_mul_add _ h1]
    rcases j with _ | j
    · simp only [Nat.mul_zero, Nat.zero_add, hb, if_true, and_one_mul_testBit Z c b hc]
      simp
    · have hj : ¬ (8 * (j + 1) + b < 8) := by omega
      rw [if_neg hj, show 8 * (j + 1) + b - 8 = 8 * j + b by omega,
        lanes_mul_testBit n (Z >>> 8) c hc j b hb, Nat.testBit_shiftRight]
      rw [show 8 + 8 * j = 8 * (j + 1) by omega]
      simp

theorem lanes_eight : lanes 8 = 72340172838076673 := by decide

@[expose] def term (X Y i : ℕ) : ℕ := ((Y >>> i) &&& lanes 8) * ((X >>> (8 * i)) &&& 255)

theorem term_testBit (X Y i j b : ℕ) (hj : j < 8) (hb : b < 8) :
    (term X Y i).testBit (8 * j + b) = (Y.testBit (8 * j + i) && X.testBit (8 * i + b)) := by
  have hc : (X >>> (8 * i)) &&& 255 < 2 ^ 8 := lt_of_le_of_lt Nat.and_le_right (by norm_num)
  rw [term, lanes_mul_testBit 8 _ _ hc j b hb, Nat.testBit_shiftRight, Nat.testBit_and,
    Nat.testBit_shiftRight]
  have h255 : (255 : ℕ).testBit b = true := by
    interval_cases b <;> decide
  simp only [hj, decide_true, Bool.true_and, h255, Bool.and_true]
  rw [Nat.add_comm i, Nat.add_comm (8 * i)]

@[expose] def mulPs (X Y : ℕ) : ℕ :=
  term X Y 0 ^^^ (term X Y 1 ^^^ (term X Y 2 ^^^ (term X Y 3 ^^^ (term X Y 4 ^^^ (term X Y 5 ^^^
    (term X Y 6 ^^^ term X Y 7))))))

@[expose] def byte (X j : ℕ) : ℕ := (X >>> (8 * j)) &&& 255

theorem byte_testBit (X j b : ℕ) :
    (byte X j).testBit b = (decide (b < 8) && X.testBit (8 * j + b)) := by
  rw [byte, Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hb : b < 8
  · have h255 : (255 : ℕ).testBit b = true := by
      interval_cases b <;> decide
    simp [hb, h255]
  · have h255 : (255 : ℕ).testBit b = false := by
      apply Nat.testBit_eq_false_of_lt
      calc (255 : ℕ) < 2 ^ 8 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    simp [hb, h255]

theorem testBit_ite (c : Bool) (a b : ℕ) : (if c then a else 0).testBit b = (c && a.testBit b) := by
  cases c <;> simp

@[expose] def unpackS (X : ℕ) : List ℕ :=
  [byte X 0, byte X 1, byte X 2, byte X 3, byte X 4, byte X 5, byte X 6, byte X 7]

theorem col_eq (X Y j : ℕ) (hj : j < 8) :
    mv8 (unpackS X) (byte Y j) = byte (mulPs X Y) j := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [mv8, unpackS, bt, List.getD_cons_zero, List.getD_cons_succ, Nat.testBit_xor,
    testBit_ite, byte_testBit]
  by_cases hb : b < 8
  · simp only [hb, decide_true, Bool.true_and, mulPs, Nat.testBit_xor, term_testBit X Y _ j b hj hb]
    norm_num
  · simp [hb]

theorem mul8_unpackS (X Y : ℕ) : mul8 (unpackS X) (unpackS Y) = unpackS (mulPs X Y) := by
  have hY : unpackS Y = [byte Y 0, byte Y 1, byte Y 2, byte Y 3, byte Y 4, byte Y 5, byte Y 6,
    byte Y 7] := rfl
  rw [mul8, hY]
  simp only [List.map_cons, List.map_nil]
  rw [col_eq X Y 0 (by norm_num), col_eq X Y 1 (by norm_num), col_eq X Y 2 (by norm_num),
    col_eq X Y 3 (by norm_num), col_eq X Y 4 (by norm_num), col_eq X Y 5 (by norm_num),
    col_eq X Y 6 (by norm_num), col_eq X Y 7 (by norm_num)]
  rfl

theorem mulP_eq (X Y : ℕ) : mulP X Y = mulPs X Y := by
  simp only [mulPs, term, lanes_eight]
  rfl

theorem unpackM_eq (X : ℕ) : unpackM X = unpackS X := rfl

theorem mul8_unpackM (X Y : ℕ) : mul8 (unpackM X) (unpackM Y) = unpackM (mulP X Y) := by
  rw [unpackM_eq, unpackM_eq, unpackM_eq, mul8_unpackS, mulP_eq]

theorem code64R_eq : code64R = code64 := rfl

theorem byte_lt (X j : ℕ) : byte X j < 256 :=
  lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem byte_eq (X j : ℕ) : byte X j = X / 256 ^ j % 256 := by
  rw [byte, Nat.shiftRight_eq_div_pow, show (255 : ℕ) = 2 ^ 8 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num

theorem code64_unpackS (X : ℕ) : code64 (unpackS X) = X % 2 ^ 64 := by
  simp only [code64, unpackS, List.foldr_cons, List.foldr_nil, byte_eq]
  omega

theorem unpackS_code64 (A : List ℕ) (h : validB A = true) : unpackS (code64 A) = A := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hl, hc⟩ := h
  match A, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7], _ =>
    have h0 := hc a0 (by simp)
    have h1 := hc a1 (by simp)
    have h2 := hc a2 (by simp)
    have h3 := hc a3 (by simp)
    have h4 := hc a4 (by simp)
    have h5 := hc a5 (by simp)
    have h6 := hc a6 (by simp)
    have h7 := hc a7 (by simp)
    simp only [unpackS, code64, List.foldr_cons, List.foldr_nil, byte_eq, List.cons.injEq,
      and_true]
    omega

theorem unpackM_code64R (A : List ℕ) (h : validB A = true) : unpackM (code64R A) = A := by
  rw [unpackM_eq, code64R_eq, unpackS_code64 A h]

theorem validB_unpackM (X : ℕ) : validB (unpackM X) = true := by
  rw [unpackM_eq]
  simp only [validB, unpackS, List.length_cons, List.length_nil, List.all_cons, List.all_nil,
    byte_lt, decide_true, Bool.and_true]
  rfl

theorem unpackM_inj {X Y : ℕ} (hX : X < 2 ^ 64) (hY : Y < 2 ^ 64) (h : unpackM X = unpackM Y) :
    X = Y := by
  have := congrArg code64 h
  rw [unpackM_eq, unpackM_eq, code64_unpackS, code64_unpackS, Nat.mod_eq_of_lt hX,
    Nat.mod_eq_of_lt hY] at this
  exact this

theorem term_lt (X Y i : ℕ) : term X Y i < 2 ^ 64 := by
  have h1 : (Y >>> i) &&& lanes 8 ≤ lanes 8 := Nat.and_le_right
  have h2 : (X >>> (8 * i)) &&& 255 ≤ 255 := Nat.and_le_right
  rw [term]
  calc ((Y >>> i) &&& lanes 8) * ((X >>> (8 * i)) &&& 255) ≤ lanes 8 * 255 :=
        Nat.mul_le_mul h1 h2
    _ < 2 ^ 64 := by rw [lanes_eight]; norm_num

theorem mulP_lt (X Y : ℕ) : mulP X Y < 2 ^ 64 := by
  rw [mulP_eq, mulPs]
  repeat' apply Nat.xor_lt_two_pow
  all_goals exact term_lt _ _ _

theorem oneP_eq : unpackM oneP = one8 := by decide

theorem oneP_lt : oneP < 2 ^ 64 := by decide

theorem mv8R_eq (A : List ℕ) (v : ℕ) : mv8R A v = mv8 A v := by
  match A with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: _ =>
    have hb : ∀ (a i : ℕ), Nat.mul a (Nat.land (Nat.shiftRight v i) 1) =
        if bt v i then a else 0 := by
      intro a i
      change a * ((v >>> i) &&& 1) = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, bt, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ i) with h | h <;> simp [h]
    have h0 : Nat.land v 1 = Nat.land (Nat.shiftRight v 0) 1 := rfl
    simp only [mv8R, mv8, List.getD_cons_zero, List.getD_cons_succ]
    rw [h0, hb, hb, hb, hb, hb, hb, hb, hb]
    rfl
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl

theorem mul8F_eq (A B : List ℕ) : mul8F A B = mul8 A B := by
  rw [mul8F]
  split_ifs with h
  · rw [Bool.and_eq_true] at h
    rw [← mul8_unpackM, unpackM_code64R A h.1, unpackM_code64R B h.2]
  · rw [mul8]
    exact List.map_congr_left (fun v _ => mv8R_eq A v)

theorem mul8_toF (A B : List ℕ) : mul8 A B = mul8F A B := (mul8F_eq A B).symm

theorem mv8_toR (A : List ℕ) (v : ℕ) : mv8 A v = mv8R A v := (mv8R_eq A v).symm

theorem beq_symm {α : Type} [BEq α] [LawfulBEq α] (x y : α) : (x == y) = (y == x) := by
  by_cases h : x = y
  · subst h
    rfl
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]

theorem ntMem_tip {α : Type} [BEq α] (d k : ℕ) (xs : List α) (y : α) :
    ntMem d k (.tip xs) y = xs.elem y := by
  cases d <;> rfl

theorem ntMem_zero_node {α : Type} [BEq α] (k : ℕ) (l r : NT α) (y : α) :
    ntMem 0 k (.node l r) y = false := rfl

theorem ntMem_succ_node {α : Type} [BEq α] (d k : ℕ) (l r : NT α) (y : α) :
    ntMem (d + 1) k (.node l r) y = Bool.rec (ntMem d (Nat.shiftRight k 1) r y)
      (ntMem d (Nat.shiftRight k 1) l y) (Nat.beq (Nat.land k 1) 0) := rfl

theorem ntIns_zero_tip {α : Type} (k : ℕ) (xs : List α) (x : α) :
    ntIns 0 k (.tip xs) x = .tip (x :: xs) := rfl

theorem ntIns_zero_node {α : Type} (k : ℕ) (l r : NT α) (x : α) :
    ntIns 0 k (.node l r) x = .tip [x] := rfl

theorem ntIns_succ_tip {α : Type} (d k : ℕ) (xs : List α) (x : α) :
    ntIns (d + 1) k (.tip xs) x = Bool.rec (.node (.tip xs) (ntIns d (Nat.shiftRight k 1) (.tip xs) x))
      (.node (ntIns d (Nat.shiftRight k 1) (.tip xs) x) (.tip xs)) (Nat.beq (Nat.land k 1) 0) := rfl

theorem ntIns_succ_node {α : Type} (d k : ℕ) (l r : NT α) (x : α) :
    ntIns (d + 1) k (.node l r) x = Bool.rec (.node l (ntIns d (Nat.shiftRight k 1) r x))
      (.node (ntIns d (Nat.shiftRight k 1) l x) r) (Nat.beq (Nat.land k 1) 0) := rfl

theorem ntMem_ins {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (d kx ky : ℕ) (t : NT α) (x y : α), (x = y → kx = ky) →
      ntMem d ky (ntIns d kx t x) y = (x == y || ntMem d ky t y)
  | 0, _, _, .tip xs, x, y, _ => by
    rw [ntIns_zero_tip, ntMem_tip, ntMem_tip, List.elem_cons, beq_symm]
    cases x == y <;> rfl
  | 0, _, _, .node _ _, x, y, _ => by
    rw [ntIns_zero_node, ntMem_tip, ntMem_zero_node, List.elem_cons, List.elem_nil, beq_symm]
    cases x == y <;> rfl
  | d + 1, kx, ky, .tip xs, x, y, h => by
    have h' : x = y → Nat.shiftRight kx 1 = Nat.shiftRight ky 1 := fun e => by rw [h e]
    have ih := ntMem_ins d (Nat.shiftRight kx 1) (Nat.shiftRight ky 1) (.tip xs) x y h'
    rw [ntIns_succ_tip, ntMem_tip]
    cases hx : Nat.beq (Nat.land kx 1) 0 <;> cases hy : Nat.beq (Nat.land ky 1) 0 <;>
      dsimp only <;> rw [ntMem_succ_node] <;> rw [hy] <;> dsimp only <;>
      first
        | (rw [ih, ntMem_tip])
        | (rw [ntMem_tip]
           have hne : (x == y) = false := by
             rw [beq_eq_false_iff_ne]
             intro e
             have := h e
             subst this
             rw [hx] at hy
             exact absurd hy (by simp)
           rw [hne, Bool.false_or])
  | d + 1, kx, ky, .node l r, x, y, h => by
    have h' : x = y → Nat.shiftRight kx 1 = Nat.shiftRight ky 1 := fun e => by rw [h e]
    rw [ntIns_succ_node, ntMem_succ_node]
    cases hx : Nat.beq (Nat.land kx 1) 0 <;> cases hy : Nat.beq (Nat.land ky 1) 0 <;>
      dsimp only <;> rw [ntMem_succ_node] <;> rw [hy] <;> dsimp only <;>
      first
        | (rw [ntMem_ins d _ _ _ x y h'])
        | (have hne : (x == y) = false := by
             rw [beq_eq_false_iff_ne]
             intro e
             have := h e
             subst this
             rw [hx] at hy
             exact absurd hy (by simp)
           rw [hne, Bool.false_or])

theorem memP_insP (t : NT ℕ) (x y : ℕ) : memP (insP t x) y = (x == y || memP t y) :=
  ntMem_ins 16 _ _ t x y (fun e => by rw [e])

theorem memP_empty (y : ℕ) : memP (.tip []) y = false := by
  rw [memP, ntMem_tip]
  rfl

theorem memP_foldl (L : List ℕ) :
    ∀ (t : NT ℕ) (y : ℕ), memP (L.foldl insP t) y = (L.contains y || memP t y) := by
  induction L with
  | nil => intro t y; simp
  | cons a L ih =>
    intro t y
    rw [List.foldl_cons, ih, memP_insP, List.contains_cons, beq_symm a y]
    cases L.contains y <;> cases (y == a) <;> cases memP t y <;> rfl

theorem memP_ofListP (L : List ℕ) (y : ℕ) : memP (ofListP L) y = L.contains y := by
  rw [ofListP, memP_foldl, memP_empty, Bool.or_false]

theorem memLR_insLR (t : NT (List ℕ)) (x y : List ℕ) :
    memLR (insLR t x) y = (x == y || memLR t y) :=
  ntMem_ins 16 _ _ t x y (fun e => by rw [e])

theorem memLR_empty (y : List ℕ) : memLR (.tip []) y = false := by
  rw [memLR, ntMem_tip]
  rfl

theorem memLR_foldl (L : List (List ℕ)) :
    ∀ (t : NT (List ℕ)) (y : List ℕ), memLR (L.foldl insLR t) y = (L.contains y || memLR t y) := by
  induction L with
  | nil => intro t y; simp
  | cons a L ih =>
    intro t y
    rw [List.foldl_cons, ih, memLR_insLR, List.contains_cons, beq_symm a y]
    cases L.contains y <;> cases (y == a) <;> cases memLR t y <;> rfl

theorem memLR_ofListLR (L : List (List ℕ)) (y : List ℕ) :
    memLR (ofListLR L) y = L.contains y := by
  rw [ofListLR, memLR_foldl, memLR_empty, Bool.or_false]

theorem nodupPAux_iff : ∀ (l : List ℕ) (t : NT ℕ),
    nodupPAux t l = true ↔ l.Nodup ∧ ∀ x ∈ l, memP t x = false
  | [], t => by simp [nodupPAux]
  | x :: l, t => by
    rw [nodupPAux, Bool.and_eq_true, nodupPAux_iff l (insP t x), List.nodup_cons]
    simp only [Bool.not_eq_true', memP_insP, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
      List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨fun hx => (h3 x hx).1 rfl, h2⟩, h1, fun y hy => (h3 y hy).2⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h3, h2, fun y hy => ⟨fun e => h1 (e ▸ hy), h4 y hy⟩⟩

theorem nodupP_iff (l : List ℕ) : nodupP l = true ↔ l.Nodup := by
  rw [nodupP, nodupPAux_iff]
  simp [memP_empty]

theorem hs_contains_toLR (L : List (List ℕ)) (y : List ℕ) :
    (Std.HashSet.ofList L).contains y = memLR (ofListLR L) y := by
  rw [Std.HashSet.contains_ofList, memLR_ofListLR]

theorem hs_contains_toLR' (L : List (List ℕ)) :
    (Std.HashSet.ofList L).contains = memLR (ofListLR L) := by
  funext y
  exact hs_contains_toLR L y

theorem hsN_contains_toP (L : List ℕ) (y : ℕ) :
    (Std.HashSet.ofList L).contains y = memP (ofListP L) y := by
  rw [Std.HashSet.contains_ofList, memP_ofListP]

theorem hsN_contains_toP' (L : List ℕ) :
    (Std.HashSet.ofList L).contains = memP (ofListP L) := by
  funext y
  exact hsN_contains_toP L y

theorem contains_toLR (L : List (List ℕ)) (y : List ℕ) : L.contains y = memLR (ofListLR L) y :=
  (memLR_ofListLR L y).symm

theorem isChain_mergeSort_iff (l : List ℕ) :
    (l.mergeSort).IsChain (· < ·) ↔ l.Nodup := by
  have hs : (l.mergeSort).Pairwise (fun a b => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
  have hs' : (l.mergeSort).Pairwise (· ≤ ·) := hs.imp (fun h => by simpa using h)
  rw [List.isChain_iff_pairwise, ← (List.mergeSort_perm l _).nodup_iff]
  constructor
  · intro h
    exact h.imp (fun h => ne_of_lt h)
  · intro h
    exact (hs'.and h).imp (fun h => lt_of_le_of_ne h.1 h.2)

theorem decide_isChain_toP (l : List ℕ) :
    decide ((l.mergeSort).IsChain (· < ·)) = nodupP l := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, nodupP_iff, isChain_mergeSort_iff]

theorem nodupB_toP (L : List (List ℕ)) : nodupB L = nodupP (L.map code64R) := by
  rw [nodupB, decide_isChain_toP, code64R_eq]

theorem unpackM_beq {X Y : ℕ} (hX : X < 2 ^ 64) (hY : Y < 2 ^ 64) :
    (unpackM X == unpackM Y) = (X == Y) := by
  by_cases h : X = Y
  · subst h
    simp
  · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (fun e => h (unpackM_inj hX hY e))]

theorem getD_unpack (gens : List (List ℕ)) (hg : gens.all validB = true) (i : ℕ) :
    gens.getD i one8 = unpackM ((gens.map code64R).getD i oneP) := by
  rw [List.all_eq_true] at hg
  by_cases hi : i < gens.length
  · rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map, unpackM_code64R _ (hg _ (List.getElem_mem hi))]
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hi),
      oneP_eq]

def PRel (gens : List (List ℕ))
    (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT ℕ × List ℕ × List ℕ) : Prop :=
  a.2.1.map (evalW gens) = b.2.1.map unpackM ∧ a.2.2.map Prod.snd = b.2.2.map unpackM ∧
    (∀ p ∈ a.2.2, p.2 = evalW gens p.1) ∧ (∀ q ∈ b.2.1, q < 2 ^ 64) ∧ (∀ q ∈ b.2.2, q < 2 ^ 64) ∧
    ∀ q, q < 2 ^ 64 → a.1.contains (unpackM q) = memP b.1 q

def stepH (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ) :=
  let y := mul8 (gens.getD i one8) wx.2
  if st.1.contains y then st else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)

def stepP (gp : List ℕ) (x : ℕ) (st : NT ℕ × List ℕ × List ℕ) (i : ℕ) : NT ℕ × List ℕ × List ℕ :=
  let y := mulP (gp.getD i oneP) x
  if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)

theorem stepRelP (gens : List (List ℕ)) (hg : gens.all validB = true) (wx : List ℕ × List ℕ)
    (x : ℕ) (hwx : wx.2 = evalW gens wx.1) (hx : wx.2 = unpackM x) (i : ℕ)
    (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT ℕ × List ℕ × List ℕ) (h : PRel gens a b) :
    PRel gens (stepH gens wx a i) (stepP (gens.map code64R) x b i) := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  obtain ⟨h2, h3, h4, h5, h6, h1⟩ := h
  dsimp only at h2 h3 h4 h5 h6 h1
  unfold stepH stepP
  dsimp only
  have hy : mul8 (gens.getD i one8) wx.2 = unpackM (mulP ((gens.map code64R).getD i oneP) x) := by
    rw [getD_unpack gens hg i, hx, mul8_unpackM]
  have hlt := mulP_lt ((gens.map code64R).getD i oneP) x
  have hev : evalW gens (i :: wx.1) = mul8 (gens.getD i one8) wx.2 := by
    rw [hwx]
    rfl
  rw [hy, h1 _ hlt]
  by_cases hc : memP b1 (mulP ((gens.map code64R).getD i oneP) x) = true
  · rw [if_pos hc, if_pos hc]
    exact ⟨h2, h3, h4, h5, h6, h1⟩
  · rw [if_neg hc, if_neg hc]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, h2, hev, hy]
    · simp only [List.map_cons, h3]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact (hev.trans hy).symm
      · exact h4 p hp
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hlt
      · exact h5 q hq
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hlt
      · exact h6 q hq
    · intro q hq
      dsimp only
      rw [Std.HashSet.contains_insert, memP_insP, h1 q hq, unpackM_beq hlt hq]

theorem foldl_inner (gens : List (List ℕ)) (hg : gens.all validB = true) (wx : List ℕ × List ℕ)
    (x : ℕ) (hwx : wx.2 = evalW gens wx.1) (hx : wx.2 = unpackM x) :
    ∀ (l : List ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
      (b : NT ℕ × List ℕ × List ℕ), PRel gens a b →
      PRel gens (l.foldl (stepH gens wx) a) (l.foldl (stepP (gens.map code64R) x) b)
  | [], _, _, h => h
  | i :: l, a, b, h =>
    foldl_inner gens hg wx x hwx hx l _ _ (stepRelP gens hg wx x hwx hx i a b h)

theorem foldl_outer (gens : List (List ℕ)) (hg : gens.all validB = true) :
    ∀ (fr : List (List ℕ × List ℕ)) (frP : List ℕ), fr.map Prod.snd = frP.map unpackM →
      (∀ p ∈ fr, p.2 = evalW gens p.1) →
      ∀ (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
        (b : NT ℕ × List ℕ × List ℕ), PRel gens a b →
        PRel gens (fr.foldl (fun st wx => (List.range gens.length).foldl (stepH gens wx) st) a)
          (frP.foldl (fun st x => (List.range gens.length).foldl
            (stepP (gens.map code64R) x) st) b)
  | [], [], _, _, _, _, h => h
  | [], _ :: _, he, _, _, _, _ => by simp at he
  | _ :: _, [], he, _, _, _, _ => by simp at he
  | wx :: fr, x :: frP, he, hfr, a, b, h => by
    simp only [List.map_cons, List.cons.injEq] at he
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_outer gens hg fr frP he.2 (fun p hp => hfr p (List.mem_cons_of_mem _ hp)) _ _
      (foldl_inner gens hg wx x (hfr wx List.mem_cons_self) he.1 _ a b h)

theorem bfsW_eqP (gens : List (List ℕ)) (hg : gens.all validB = true) (cap : ℕ) :
    ∀ (fuel : ℕ) (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
      (b : NT ℕ × List ℕ × List ℕ), PRel gens a b →
      (bfsW gens cap fuel a.1 a.2.1 a.2.2).map (evalW gens) =
        (bfsP (gens.map code64R) cap fuel b.1 b.2.1 b.2.2).map unpackM
  | 0, a, b, h => h.1
  | fuel + 1, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, h => by
    obtain ⟨h2, h3, h4, h5, h6, h1⟩ := h
    dsimp only at h2 h3 h4 h5 h6 h1 ⊢
    have hlen : a2.length = b2.length := by
      have := congrArg List.length h2
      simpa using this
    match a3, b3, h3 with
    | [], [], _ => simp only [bfsW, bfsP]; exact h2
    | [], _ :: _, he => simp at he
    | _ :: _, [], he => simp at he
    | wx :: fr, x :: frP, he =>
      simp only [bfsW, bfsP, List.length_map]
      rw [hlen]
      split_ifs with hc
      · exact h2
      · have hrel := foldl_outer gens hg (wx :: fr) (x :: frP) he h4 (a1, a2, [])
          (b1, b2, []) ⟨h2, rfl, by simp, h5, by simp, h1⟩
        exact bfsW_eqP gens hg cap fuel _ _ hrel

theorem elemsOf_eqP (gens : List (List ℕ)) (hg : gens.all validB = true) (cap : ℕ) :
    elemsOf gens cap = (elemsP (gens.map code64R) cap).map unpackM := by
  rw [elemsOf, wordsOf, elemsP]
  refine bfsW_eqP gens hg cap 200 (((∅ : Std.HashSet (List ℕ)).insert one8), [[]], [([], one8)])
    (insP (.tip []) oneP, [oneP], [oneP]) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalW, oneP_eq]
  · simp [oneP_eq]
  · simp [evalW]
  · simpa using oneP_lt
  · simpa using oneP_lt
  · intro q hq
    dsimp only
    rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty,
      ← oneP_eq, unpackM_beq oneP_lt hq]

theorem elemsOf_toF (gens : List (List ℕ)) (cap : ℕ) : elemsOf gens cap = elemsF gens cap := by
  rw [elemsF]
  split_ifs with hg
  · exact elemsOf_eqP gens hg cap
  · rfl

end CFSG.KC.Mat8P

end
