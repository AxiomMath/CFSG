module

public import CFSG.Certificates.Kernel.SmithEK.LaneSound
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

theorem coord_xor (x y i : Nat) : coord (x ^^^ y) i = coord x i ^^^ coord y i := by
  have h4 : ∀ z, coord z i = z / 2 ^ (2 * i) % 2 ^ 2 := fun z => by
    unfold coord
    rw [pow_mul]
    norm_num
  rw [h4, h4, h4]
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < 2) <;> simp

theorem coord_lt (x i : Nat) : coord x i < 4 := Nat.mod_lt _ (by norm_num)

theorem f4_sq_xor : ∀ a < 4, ∀ b < 4, ∀ c < 4,
    f4mul c (f4mul (a ^^^ b) (a ^^^ b)) = f4mul c (f4mul a a) ^^^ f4mul c (f4mul b b) := by
  decide

theorem foldl_xor_split (f g : Nat → Nat) : ∀ (L : List Nat) (a b : Nat),
    L.foldl (fun acc i => acc ^^^ (f i ^^^ g i)) (a ^^^ b) =
      L.foldl (fun acc i => acc ^^^ f i) a ^^^ L.foldl (fun acc i => acc ^^^ g i) b
  | [], _, _ => rfl
  | i :: L, a, b => by
    simp only [List.foldl_cons]
    rw [← foldl_xor_split f g L]
    congr 1
    rw [Nat.xor_assoc, Nat.xor_assoc]
    congr 1
    rw [← Nat.xor_assoc, Nat.xor_comm b, Nat.xor_assoc]

theorem hermC_xor (p x y : Nat) : hermC p (x ^^^ y) = hermC p x ^^^ hermC p y := by
  unfold hermC
  have e : ∀ i, f4mul (coord p i) (f4mul (coord (x ^^^ y) i) (coord (x ^^^ y) i)) =
      f4mul (coord p i) (f4mul (coord x i) (coord x i)) ^^^
        f4mul (coord p i) (f4mul (coord y i) (coord y i)) := fun i => by
    rw [coord_xor]
    exact f4_sq_xor _ (coord_lt _ _) _ (coord_lt _ _) _ (coord_lt _ _)
  simp only [e]
  rw [← foldl_xor_split, Nat.zero_xor]

theorem hermC_zero (p : Nat) : hermC p 0 = 0 := by
  unfold hermC
  simp [coord, f4mul]

theorem hermC_lt (p d : Nat) : hermC p d < 4 := by
  unfold hermC
  have : ∀ (L : List Nat) (a : Nat), a < 4 →
      L.foldl (fun acc i => acc ^^^ f4mul (coord p i) (f4mul (coord d i) (coord d i))) a < 4 := by
    intro L
    induction L with
    | nil => exact fun a ha => ha
    | cons i L ih =>
      intro a ha
      exact ih _ (Nat.xor_lt_two_pow (n := 2) ha (f4mul_lt _ _))
  exact this _ 0 (by norm_num)

theorem foldr_xor_init (t : Nat → Nat) : ∀ (bs : List Nat) (a : Nat),
    bs.foldr (fun b acc => t b ^^^ acc) a = bs.foldr (fun b acc => t b ^^^ acc) 0 ^^^ a
  | [], a => by simp
  | b :: bs, a => by
    simp only [List.foldr_cons]
    rw [foldr_xor_init t bs a, Nat.xor_assoc]

theorem hermC_foldr (p : Nat) (y : Nat → Nat) : ∀ (bs : List Nat),
    hermC p (bs.foldr (fun b acc => y b ^^^ acc) 0) =
      bs.foldr (fun b acc => hermC p (y b) ^^^ acc) 0
  | [] => hermC_zero p
  | b :: bs => by
    simp only [List.foldr_cons]
    rw [hermC_xor, hermC_foldr p y bs]

theorem foldr_bits (q : Nat) : ∀ n, (List.range n).foldr
    (fun b acc => (if (q >>> b) % 2 = 1 then 2 ^ b else 0) ^^^ acc) 0 = q % 2 ^ n
  | 0 => by simp [Nat.mod_one]
  | n + 1 => by
    have tb : ∀ m, q.testBit m = decide ((q >>> m) % 2 = 1) := fun m => by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, Nat.xor_zero,
      foldr_xor_init, foldr_bits q n]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    split_ifs with h
    · rw [Nat.testBit_two_pow]
      have hq : q.testBit n = true := by
        rw [tb]
        exact decide_eq_true h
      by_cases hj : j = n
      · subst hj
        simp [hq]
      · have : n = j ↔ False := ⟨fun e => hj e.symm, False.elim⟩
        by_cases hj' : j < n
        · simp [hj', hj, show j < n + 1 by omega, this]
        · simp [hj', show ¬ j < n + 1 by omega, this]
    · have hq : q.testBit n = false := by
        rw [tb]
        have : (q >>> n) % 2 = 0 := by omega
        simp [this]
      rw [Nat.zero_testBit, Bool.xor_false]
      by_cases hj : j < n
      · simp [hj, show j < n + 1 by omega]
      · by_cases hjn : j = n
        · subst hjn
          simp [hq]
        · simp [hj, show ¬ j < n + 1 by omega]

theorem selX_foldr (x c : Nat → Nat) (hc : ∀ b, c b ≤ 1) : ∀ (bs : List Nat),
    selX (bs.map x) (bs.foldr (fun b acc => c b + 2 * acc) 0) =
      bs.foldr (fun b acc => (if c b = 1 then x b else 0) ^^^ acc) 0
  | [] => rfl
  | b :: bs => by
    have e : ∀ (y : Nat) (L : List Nat) (s : Nat),
        selX (y :: L) s = (if s % 2 == 1 then y else 0) ^^^ selX L (s / 2) := fun _ _ _ => rfl
    simp only [List.map_cons, List.foldr_cons]
    rw [e]
    have h1 : (c b + 2 * bs.foldr (fun b acc => c b + 2 * acc) 0) % 2 = c b := by
      have := hc b
      omega
    have h2 : (c b + 2 * bs.foldr (fun b acc => c b + 2 * acc) 0) / 2 =
        bs.foldr (fun b acc => c b + 2 * acc) 0 := by
      have := hc b
      omega
    rw [h1, h2, selX_foldr x c hc bs]
    congr 1
    by_cases h : c b = 1
    · simp [h]
    · simp [h]

theorem hM_eq (p i : Nat) :
    hM p i = (List.range 12).foldr (fun b acc => (hermC p (2 ^ b) >>> i) % 2 + 2 * acc) 0 := by
  unfold hM
  rfl

theorem bit_xor (i a b : Nat) : (a ^^^ b) >>> i % 2 = ((a >>> i) % 2) ^^^ ((b >>> i) % 2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  simp only [Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow, Nat.testBit_div_two_pow,
    Nat.testBit_xor]
  have h2 : ∀ z : Nat, z % 2 = z % 2 ^ 1 := fun z => by norm_num
  rw [h2, h2, h2, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (j < 1) <;> simp

theorem bit_foldr (i : Nat) (t : Nat → Nat) : ∀ (bs : List Nat),
    (bs.foldr (fun b acc => t b ^^^ acc) 0) >>> i % 2 =
      bs.foldr (fun b acc => (t b >>> i % 2) ^^^ acc) 0
  | [] => by simp
  | b :: bs => by
    simp only [List.foldr_cons]
    rw [bit_xor, bit_foldr i t bs]

theorem selX_hM (p q i : Nat) (hq : q < 4096) :
    selX ((List.range 12).map fun b => (q >>> b) % 2) (hM p i) = (hermC p q >>> i) % 2 := by
  rw [hM_eq, selX_foldr _ _ (fun b => by omega)]
  have hq' : q = q % 2 ^ 12 := (Nat.mod_eq_of_lt (by norm_num; omega)).symm
  conv_rhs => rw [hq', ← foldr_bits q 12, hermC_foldr, bit_foldr]
  congr 1
  funext b acc
  congr 1
  by_cases h : (q >>> b) % 2 = 1
  · rw [if_pos h]
    by_cases h' : hermC p (2 ^ b) >>> i % 2 = 1
    · rw [if_pos h', h, h']
    · rw [if_neg h']
      omega
  · have h0 : (q >>> b) % 2 = 0 := by omega
    rw [if_neg h, hermC_zero, Nat.zero_shiftRight, h0]
    split_ifs <;> rfl

set_option exponentiation.threshold 512 in
theorem testBit_blkC (X f j : Nat) :
    (blkC X f).testBit j = (decide (j < 400) && X.testBit (400 * f + j)) := by
  unfold blkC
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem pf_eq_of_blkC {X Y : Nat} (h : ∀ f, blkC X f = blkC Y f) : X = Y := by
  apply Nat.eq_of_testBit_eq
  intro t
  have := congrArg (fun z => z.testBit (t % 400)) (h (t / 400))
  simp only [testBit_blkC, Nat.mod_lt t (by norm_num : 400 > 0), decide_true, Bool.true_and,
    Nat.div_add_mod] at this
  exact this

theorem blkC_xor (X Y f : Nat) : blkC (X ^^^ Y) f = blkC X f ^^^ blkC Y f := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_blkC, Nat.testBit_xor]
  cases decide (j < 400) <;> simp

theorem blkC_and (X Y f : Nat) : blkC (X &&& Y) f = blkC X f &&& blkC Y f := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_blkC, Nat.testBit_and]
  cases decide (j < 400) <;> simp

theorem blkC_or (X Y f : Nat) : blkC (X ||| Y) f = blkC X f ||| blkC Y f := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [testBit_blkC, Nat.testBit_or]
  cases decide (j < 400) <;> simp

set_option exponentiation.threshold 512 in
theorem blkC_zero (f : Nat) : blkC 0 f = 0 := by
  simp [blkC]

set_option exponentiation.threshold 512 in
theorem blkC_pkW400 : ∀ (L : List Nat) (l : Nat), (∀ x ∈ L, x < 2 ^ 400) →
    blkC (pkW 400 L) l = L.getD l 0
  | [], l, _ => by rw [pkW_nil, blkC_zero]; simp
  | x :: L, l, h => by
    have hx := h x List.mem_cons_self
    rw [pkW_cons]
    rcases l with _ | l
    · unfold blkC
      rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx,
        List.getD_cons_zero]
    · have e : blkC (x + 2 ^ 400 * pkW 400 L) (l + 1) = blkC (pkW 400 L) l := by
        unfold blkC
        rw [show 400 * (l + 1) = 400 + 400 * l by ring, Nat.shiftRight_add,
          Nat.shiftRight_eq_div_pow (x + 2 ^ 400 * pkW 400 L) 400,
          Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hx, Nat.zero_add]
      rw [e, List.getD_cons_succ]
      exact blkC_pkW400 L l fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem pkW_mul (w c : Nat) : ∀ (L : List Nat), pkW w L * c = pkW w (L.map (· * c))
  | [] => by simp [pkW_nil]
  | x :: L => by
    rw [List.map_cons, pkW_cons, pkW_cons, ← pkW_mul w c L]
    ring

theorem blkC_selX (l : Nat) : ∀ (Pl : List Nat) (s : Nat),
    blkC (selX Pl s) l = selX (Pl.map fun x => blkC x l) s
  | [], _ => blkC_zero l
  | x :: Pl, s => by
    have e : ∀ (y : Nat) (L : List Nat) (s : Nat),
        selX (y :: L) s = (if s % 2 == 1 then y else 0) ^^^ selX L (s / 2) := fun _ _ _ => rfl
    rw [List.map_cons, e, e, blkC_xor, blkC_selX l Pl (s / 2)]
    congr 1
    split_ifs
    · rfl
    · exact blkC_zero l

set_option exponentiation.threshold 512 in
theorem fld_full {m : Nat} (hm : m < 20) : fld m (2 ^ 400 - 1) = 2 ^ 20 - 1 := by
  interval_cases m <;> decide

theorem rowsF_get {ONE REP DATA Bpk : Nat} {Qs Pl : List Nat} :
    ∀ (R : List Nat) (Cr : List (List Nat)) (Pr : List Nat),
      rowsF ONE REP DATA Bpk Qs Pl R Cr Pr = true → Pr = Cr.map (pkW 20) →
      ∀ i < R.length, rowF ONE REP DATA Bpk Qs Pl (R.getD i 0) (Cr.getD i [])
        (pkW 20 (Cr.getD i [])) = true
  | [], _, _, _, _, i, hi => absurd hi (by simp)
  | p :: R, Cr, Pr, h, hP, i, hi => by
    subst hP
    have h' : (rowF ONE REP DATA Bpk Qs Pl p (Cr.headD []) ((Cr.map (pkW 20)).headD 0) &&
        rowsF ONE REP DATA Bpk Qs Pl R Cr.tail (Cr.map (pkW 20)).tail) = true := h
    rw [Bool.and_eq_true] at h'
    rcases i with _ | i
    · cases Cr with
      | nil => simpa [pkW_nil] using h'.1
      | cons A Cr => simpa using h'.1
    · have e := rowsF_get R Cr.tail _ h'.2 (List.map_tail ..).symm i (by simpa using hi)
      cases Cr with
      | nil => simpa using e
      | cons A Cr => simpa using e

set_option exponentiation.threshold 512 in
theorem chkPF_sound {P : List Nat} {C : List (List Nat)} (h : chkPF P C = true) :
    ∀ k < P.length, ∀ l < P.length,
      (hermC (P.getD k 0) (P.getD l 0) = 0 → ∀ m < 20,
        applyL (C.getD k []) ((C.getD l []).getD m 0) =
          applyL (C.getD l []) ((C.getD k []).getD m 0)) ∧
      (hermC (P.getD k 0) (P.getD l 0) ≠ 0 → ∀ m < 20,
        applyL (C.getD k []) (applyL (C.getD l []) ((C.getD k []).getD m 0)) =
          applyL (C.getD l []) (applyL (C.getD k []) ((C.getD l []).getD m 0))) := by
  unfold chkPF at h
  set_option simprocs false in
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hPl, hCl⟩, hPb⟩, hmemC⟩, hrows⟩ := h
  have getC : ∀ l < 693, C.getD l [] ∈ C := fun l hl => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have getP : ∀ l < 693, P.getD l 0 < 4096 := fun l hl => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hPb _ (List.getElem_mem _)
  have hxeq : ∀ {a b : Nat}, a ^^^ b = 0 → a = b := fun {a b} e => by
    have := congrArg (· ^^^ b) e
    simpa [Nat.xor_assoc, Nat.xor_self] using this
  have hO : ∀ s, fld s (pkW 400 (List.replicate 693 1) * l20) ≤ 1 := fun s => by
    rw [fld_ONE]
    split_ifs <;> omega
  have hO1 : ∀ s < 13860, fld s (pkW 400 (List.replicate 693 1) * l20) = 1 := fun s hs => by
    rw [fld_ONE, if_pos hs]
  have hQb : ∀ x ∈ C.map (pkW 20), x < 2 ^ 400 := fun x hx => by
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hcl, hcb⟩ := hmemC c hcm
    have := pkW_lt c hcb
    rwa [hcl] at this
  have hRb : ∀ y < 2 ^ 400, ∀ x ∈ List.replicate 693 y, x < 2 ^ 400 := fun y hy x hx => by
    rw [List.eq_of_mem_replicate hx]
    exact hy
  have hq : ∀ l < 693, ∀ m < 20, (qsOf C).map (fld (20 * l + m)) = C.getD l [] := by
    intro a ha m hm
    obtain ⟨hCl', hCb⟩ := hmemC (C.getD a []) (getC a ha)
    apply List.ext_getElem (by unfold qsOf; rw [List.length_map, List.length_map,
      List.length_range, hCl'])
    intro i h1 h2
    have hi : i < 20 := by simpa [qsOf] using h1
    simp only [qsOf, List.getElem_map, List.getElem_range]
    rw [fld_pkW400 _ _ _ hm (fun x hx => by
        obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hx
        exact mul_l20_lt (getD_lt_of (hmemC c hcm).2 (by positivity) i)),
      List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      ← List.getD_eq_getElem _ [] (by omega), Nat.mul_comm,
      fld_mul_spread (getD_lt_of hCb (by positivity) i) _
        (fun t => by rw [fld_l20]; split_ifs <;> omega), fld_l20, if_pos hm, Nat.one_mul,
      List.getD_eq_getElem _ _ (by omega)]
  intro k hk l hl
  rw [hPl] at hk hl
  have hrow := rowsF_get P C _ hrows rfl k (by omega)
  have hAm := getC k hk
  generalize hA : C.getD k [] = A at hrow hAm ⊢
  obtain ⟨hAl, hAb⟩ := hmemC A hAm
  generalize hp : P.getD k 0 = p at hrow ⊢
  unfold rowF at hrow
  set_option simprocs false in
    simp only [Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨e1, e2⟩ := hrow
  have hApl : pkW 20 A < 2 ^ 400 := by
    have := pkW_lt A hAb
    rwa [hAl] at this
  have hs : ∀ m < 20, 20 * l + m < 13860 := fun m hm => by omega
  have hX : ∀ m < 20, fld (20 * l + m)
      (lmulP (pkW 400 (List.replicate 693 1) * l20) A (pkW 400 (C.map (pkW 20)))) =
      applyL A ((C.getD l []).getD m 0) := fun m hm => by
    have hfC : (C.map (pkW 20)).getD l 0 = pkW 20 (C.getD l []) := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
    rw [fld_lmulP hO A _ _ (by omega) hAb (hO1 _ (hs m hm)), fld_pkW400 _ _ _ hm hQb, hfC,
      fld_pkW20 _ _ (hmemC _ (getC l hl)).2]
  have hY : ∀ m < 20, fld (20 * l + m)
      (bmulP (pkW 400 (List.replicate 693 1) * l20) (qsOf C)
        (pkW 400 (List.replicate 693 1) * pkW 20 A)) = applyL (C.getD l []) (A.getD m 0) :=
    fun m hm => by
      rw [fld_bmulP hO _ _ _ (by simp [qsOf]) (hO1 _ (hs m hm)), hq l hl m hm, pkW_rep_mul,
        fld_pkW400 _ _ _ hm (hRb _ hApl), getD_replicate_lt hl, fld_pkW20 A m hAb]
  have hL : ∀ m < 20, ∀ Z, fld (20 * l + m) (lmulP (pkW 400 (List.replicate 693 1) * l20) A Z) =
      applyL A (fld (20 * l + m) Z) := fun m hm Z =>
    fld_lmulP hO A _ _ (by omega) hAb (hO1 _ (hs m hm))
  have hB : ∀ m < 20, ∀ Z, fld (20 * l + m) (bmulP (pkW 400 (List.replicate 693 1) * l20)
      (qsOf C) Z) = applyL (C.getD l []) (fld (20 * l + m) Z) := fun m hm Z => by
    rw [fld_bmulP hO _ _ _ (by simp [qsOf]) (hO1 _ (hs m hm)), hq l hl m hm]
  have hD : ∀ m < 20, fld (20 * l + m) (pkW 400 (List.replicate 693 1) * (2 ^ 400 - 1)) =
      2 ^ 20 - 1 := fun m hm => by
    rw [pkW_rep_mul, fld_pkW400 _ _ _ hm (hRb _ (Nat.sub_lt (by positivity) Nat.one_pos)),
      getD_replicate_lt hl, fld_full hm]
  have hMk : ∀ f, blkC ((pkW 400 (List.replicate 693 1) ^^^
      (selX (planesP P) (hM p 0) ||| selX (planesP P) (hM p 1))) &&&
        pkW 400 (List.replicate 693 1)) f =
      ((List.range 693).map fun f => if hermC p (P.getD f 0) = 0 then 1 else 0).getD f 0 := by
    intro f
    rw [blkC_and, blkC_xor, blkC_or, blkC_selX, blkC_selX,
      blkC_pkW400 _ _ (hRb _ (by norm_num))]
    by_cases hf : f < 693
    · rw [getD_replicate_lt hf, List.getD_eq_getElem _ _ (by simpa using hf), List.getElem_map,
        List.getElem_range]
      have hpl : (planesP P).map (fun x => blkC x f) =
          (List.range 12).map fun b => (P.getD f 0 >>> b) % 2 := by
        unfold planesP
        rw [List.map_map]
        apply List.map_congr_left
        intro b _
        change blkC (pkW 400 (P.map fun q => (q >>> b) % 2)) f = _
        rw [blkC_pkW400 _ _ (fun x hx => by
            obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
            exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
              (Nat.pow_le_pow_right (n := 2) (by norm_num) (by norm_num : 1 ≤ 400))),
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
          List.getD_eq_getElem _ _ (by omega)]
      rw [hpl, selX_hM _ _ _ (getP f hf), selX_hM _ _ _ (getP f hf)]
      have h4 := hermC_lt p (P.getD f 0)
      generalize hermC p (P.getD f 0) = x at h4 ⊢
      interval_cases x <;> rfl
    · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega),
        List.getD_eq_default _ _ (by rw [List.length_map, List.length_range]; omega),
        Nat.and_zero]
  have hOl : ∀ m < 20, fld (20 * l + m) (orthF (pkW 400 (List.replicate 693 1)) (planesP P) p) =
      if hermC p (P.getD l 0) = 0 then 2 ^ 20 - 1 else 0 := by
    intro m hm
    unfold orthF
    have hlt : ∀ x ∈ (List.range 693).map (fun f => if hermC p (P.getD f 0) = 0 then 1 else 0),
        x < 2 ^ 400 := fun x hx => by
      obtain ⟨f, _, rfl⟩ := List.mem_map.mp hx
      split_ifs <;> norm_num
    rw [pf_eq_of_blkC fun f => (hMk f).trans (blkC_pkW400 _ _ hlt).symm, pkW_mul,
      fld_pkW400 _ _ _ hm (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨f, _, rfl⟩ := List.mem_map.mp hy
        split_ifs
        · rw [Nat.one_mul]
          exact Nat.sub_lt (by positivity) Nat.one_pos
        · rw [Nat.zero_mul]
          positivity),
      List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_map,
      List.getElem_range]
    split_ifs
    · rw [Nat.one_mul, fld_full hm]
    · rw [Nat.zero_mul, fld_zero]
  clear hMk
  generalize pkW 400 (List.replicate 693 1) = REP at hD hX hY hL hB hOl e1 e2
  refine ⟨fun h0 m hm => ?_, fun h0 m hm => ?_⟩
  · have e := congrArg (fld (20 * l + m)) e1
    rw [fld_and, fld_xor, fld_zero, hOl m hm, if_pos h0, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (fld_lt _ _) (fld_lt _ _)), hX m hm, hY m hm] at e
    exact hxeq e
  · have e := congrArg (fld (20 * l + m)) e2
    rw [fld_and, fld_xor, fld_xor, fld_zero, hOl m hm, if_neg h0, hD m hm, Nat.xor_zero,
      Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (fld_lt _ _) (fld_lt _ _)), hL m hm, hY m hm,
      hB m hm, hX m hm] at e
    exact hxeq e

theorem chkP_of {P : List Nat} {C : List (List Nat)} (hP : uPts () = P.toArray)
    (hPl : P.length = 693) (hT : ∀ k < 693, tvCols k = (C.getD k []).toArray)
    (h : chkPF P C = true) : chkP = true := by
  have hs := chkPF_sound h
  unfold chkP
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 693 := List.mem_range.1 hk
  rw [List.all_eq_true]
  intro l hl
  have hl' : l < 693 := List.mem_range.1 hl
  rcases Nat.lt_or_ge k l with hkl | hkl
  swap
  · simp [hkl]
  have hkl' : ¬ l ≤ k := by omega
  simp only [hkl', decide_false, Bool.false_or]
  obtain ⟨hc, hb⟩ := hs k (by omega) l (by omega)
  rw [tvArr_get hk', tvArr_get hl', hT k hk', hT l hl', hP, getElem!_toArray, getElem!_toArray]
  split_ifs with h0
  · rw [beq_iff_eq] at h0
    unfold commuteB
    rw [List.all_eq_true]
    intro m hm
    rw [getElem!_toArray, getElem!_toArray, applyCols_toArray, applyCols_toArray,
      hc h0 m (List.mem_range.1 hm), beq_self_eq_true]
  · rw [beq_iff_eq] at h0
    unfold braidB
    rw [List.all_eq_true]
    intro m hm
    rw [getElem!_toArray, getElem!_toArray, applyCols_toArray, applyCols_toArray,
      applyCols_toArray, applyCols_toArray, hb h0 m (List.mem_range.1 hm), beq_self_eq_true]

end CFSG.SmithE.K
