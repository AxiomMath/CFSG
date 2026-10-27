module

public import Certificates.Data.Kernel.Misc.Oq
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill
public import Mathlib.Algebra.GroupWithZero.Nat

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_lt)

private theorem bit_eq (v j : ℕ) : bit v j = if v.testBit j then 1 else 0 := by
  have h : (v >>> j) &&& 1 = (v >>> j) % 2 := Nat.and_one_is_mod _
  have h2 : 1 &&& (v >>> j) = (v >>> j) % 2 := by rw [Nat.and_comm]; exact h
  show (v >>> j) &&& 1 = if (1 &&& v >>> j != 0) = true then 1 else 0
  rw [h, h2]
  rcases Nat.mod_two_eq_zero_or_one (v >>> j) with h0 | h0 <;> simp [h0]

private theorem fld6_eq (P i : ℕ) : fld6 P i = P / 64 ^ i % 64 := by
  have h : fld6 P i = (P >>> (6 * i)) &&& (2 ^ 6 - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem fld9_eq (P i : ℕ) : fld9 P i = P / 512 ^ i % 512 := by
  have h : fld9 P i = (P >>> (9 * i)) &&& (2 ^ 9 - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem unpack6_eq (P : ℕ) : unpack6 P = (List.range 6).map (fld6 P) := by
  unfold unpack6
  exact List.map_congr_left (fun i _ => (fld6_eq P i).symm)

private theorem unpack6_getD (P j : ℕ) (hj : j < 6) : (unpack6 P).getD j 0 = fld6 P j := by
  rw [unpack6_eq, List.getD_eq_getElem?_getD]
  simp [hj]

private theorem xorBits_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j, j < n → f j = g j) (v : ℕ) :
    xorBits n f v = xorBits n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem rec_xor (v : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.xor acc (Nat.mul (bit v j) (f j))) n : ℕ)
      = xorBits n f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (_ ^^^ (bit v n * f n)) = _
    rw [xorBits_succ, ← ih, bit_eq]
    split <;> simp

private theorem evV_xor (P v : ℕ) : evV P v = xorBits 6 (fun j => fld6 P j) v := rec_xor v _ 6

private theorem evE_xor (B e : ℕ) : evE B e = xorBits 9 (fun j => fld9 B j) e := rec_xor e _ 9

private theorem evV_eq (P v : ℕ) : evV P v = evalV (unpack6 P) v := by
  rw [evV_xor]
  exact xorBits_congr (fun j hj => (unpack6_getD P j hj).symm) v

private theorem evV_lt (P v : ℕ) : evV P v < 64 := by
  rw [evV_xor]
  exact xorBits_lt (n := 6) (fun j _ => by rw [fld6_eq]; exact Nat.mod_lt _ (by decide)) v

private noncomputable def pkW (w : ℕ) (g : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (g i) (Nat.mul w i))) n

private theorem pkW_succ (w : ℕ) (g : ℕ → ℕ) (n : ℕ) (h : pkW w g n < 2 ^ (w * n)) :
    pkW w g (n + 1) = pkW w g n + g n * 2 ^ (w * n) := by
  show (pkW w g n ||| g n <<< (w * n)) = _
  have h1 : (g n <<< (w * n)) + pkW w g n = (g n <<< (w * n)) ||| pkW w g n :=
    Nat.shiftLeft_add_eq_or_of_lt h _
  rw [Nat.or_comm, ← h1, Nat.shiftLeft_eq, Nat.add_comm]

private theorem div_step (A c X Y Z : ℕ) (hX : 0 < X) :
    (A + c * (X * (Y * Z))) / X % Y = A / X % Y := by
  have : c * (X * (Y * Z)) = X * (Y * (c * Z)) := by
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [this, Nat.add_mul_div_left _ _ hX, Nat.add_mul_mod_self_left]

private theorem pkW_spec (w : ℕ) (g : ℕ → ℕ) (n : ℕ) (hg : ∀ i, i < n → g i < 2 ^ w) :
    pkW w g n < 2 ^ (w * n) ∧ ∀ i, i < n → pkW w g n / 2 ^ (w * i) % 2 ^ w = g i := by
  induction n with
  | zero => exact ⟨by simp [pkW], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hg i (by omega))
    have hs := pkW_succ w g n h1
    have hgn := hg n (by omega)
    refine ⟨?_, fun i hi => ?_⟩
    · rw [hs, Nat.mul_succ, Nat.pow_add]
      calc pkW w g n + g n * 2 ^ (w * n) < 2 ^ (w * n) + g n * 2 ^ (w * n) := by omega
        _ = (g n + 1) * 2 ^ (w * n) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ hgn
        _ = 2 ^ (w * n) * 2 ^ w := Nat.mul_comm _ _
    · rw [hs]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · obtain ⟨m, hm⟩ : ∃ m, n = i + 1 + m := ⟨n - (i + 1), by omega⟩
        have hp : 2 ^ (w * n) = 2 ^ (w * i) * (2 ^ w * 2 ^ (w * m)) := by
          rw [hm, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.pow_add,
            Nat.mul_assoc]
        rw [hp, div_step _ _ _ _ _ (Nat.two_pow_pos _)]
        exact h2 i hi
      · rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h1, Nat.zero_add]
        exact Nat.mod_eq_of_lt hgn

private theorem fld6_eq' (P i : ℕ) : fld6 P i = P / 2 ^ (6 * i) % 2 ^ 6 := by
  rw [fld6_eq, Nat.pow_mul]; rfl

private theorem compK_eq (A B : ℕ) : compK A B = pkW 6 (fun i => evV A (fld6 B i)) 6 := rfl

private theorem compK_lt (A B : ℕ) : compK A B < 2 ^ 36 :=
  (pkW_spec 6 (fun i => evV A (fld6 B i)) 6 (fun i _ => evV_lt _ _)).1

private theorem unpack6_compK (A B : ℕ) :
    unpack6 (compK A B) = compT (unpack6 A) (unpack6 B) := by
  have h := (pkW_spec 6 (fun i => evV A (fld6 B i)) 6 (fun i _ => evV_lt _ _)).2
  calc unpack6 (compK A B) = (List.range 6).map (fld6 (compK A B)) := unpack6_eq _
    _ = (List.range 6).map (fun i => evalV (unpack6 A) (fld6 B i)) := by
      refine List.map_congr_left fun i hi => ?_
      rw [fld6_eq', ← evV_eq]
      exact h i (List.mem_range.1 hi)
    _ = compT (unpack6 A) (unpack6 B) := by
      rw [compT, unpack6_eq B, List.map_map]; rfl

private theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

private theorem wordK_letN (y : ℕ) (k : ℕ → ℕ) : wordK.letN y k = k y := by cases y <;> rfl

private theorem eqN_eq (a b : ℕ) : eqN a b = (a == b) := by
  by_cases h : a = b
  · subst h; simp [eqN, Nat.beq_refl]
  · have : Nat.beq a b = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp [eqN, this, h]

private theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

private theorem allL_iff' {L : List ℕ} {f : ℕ → Bool} : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | cons x t ih =>
    change andB (f x) (allL t f) = true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

private theorem unpack6_idK : unpack6 idK = idT := by decide +kernel

private theorem unpack6_letK (P a : ℕ) (ha : a < 4) :
    unpack6 (letK P a) = letter (unpack6 P) a := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl | rfl
  · exact (by decide +kernel : unpack6 (gamK 0) = z0T)
  · exact (by decide +kernel : unpack6 (gamK 1) = lam1T)
  · exact (by decide +kernel : unpack6 (gamK 2) = lam2T)
  · rfl

private theorem unpack6_wordK (P : ℕ) (w : List ℕ) (hw : ∀ a ∈ w, a < 4) (acc : ℕ) :
    unpack6 (wordK P w acc) =
      w.foldl (fun acc a => compT acc (letter (unpack6 P) a)) (unpack6 acc) := by
  induction w generalizing acc with
  | nil => rfl
  | cons a t ih =>
    show unpack6 (wordK.letN (compK acc (letK P a)) (wordK P t)) = _
    rw [wordK_letN, ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)), unpack6_compK,
      unpack6_letK P a (hw a (List.mem_cons_self))]
    rfl

private theorem unpack6_wordK_id (P : ℕ) (w : List ℕ) (hw : ∀ a ∈ w, a < 4) :
    unpack6 (wordK P w idK) = evalW (unpack6 P) w := by
  rw [unpack6_wordK P w hw, unpack6_idK]
  rfl

private theorem wordK_lt (P : ℕ) (w : List ℕ) (acc : ℕ) (h : acc < 2 ^ 36) :
    wordK P w acc < 2 ^ 36 := by
  induction w generalizing acc with
  | nil => exact h
  | cons a t ih =>
    show wordK.letN (compK acc (letK P a)) (wordK P t) < _
    rw [wordK_letN]
    exact ih _ (compK_lt _ _)

theorem conjK_sound' {P r : ℕ} {w : List ℕ} (h : conjK P r w = true) :
    (∀ a ∈ w, a < 3) ∧
      compT (evalW (unpack6 P) w) (unpack6 P) = compT (unpack6 r) (evalW (unpack6 P) w) := by
  change andB (lettersK w) (letB (wordK P w idK) fun g => eqN (compK g P) (compK r g)) = true at h
  rw [andB_iff, letB_eq] at h
  have hl : ∀ a ∈ w, a < 3 := fun a ha => by
    have := allL_iff'.1 h.1 a ha
    simp only [Nat.blt_eq] at this
    exact this
  refine ⟨hl, ?_⟩
  have h2 : compK (wordK P w idK) P = compK r (wordK P w idK) := Nat.eq_of_beq_eq_true h.2
  have h3 := congrArg unpack6 h2
  rw [unpack6_compK, unpack6_compK, unpack6_wordK_id P w (fun a ha => by have := hl a ha; omega)] at h3
  exact h3

private theorem outK_eq (a b : ℕ) : outK a b = outer a b := by
  show ((bit a 0 * (b &&& 7)) ^^^ ((bit a 1 * ((b &&& 7) <<< 3)) ^^^ (bit a 2 * ((b &&& 7) <<< 6))))
    = _
  rw [outer, bit_eq, bit_eq, bit_eq, Nat.xor_assoc]
  by_cases h0 : a.testBit 0 <;> by_cases h1 : a.testBit 1 <;> by_cases h2 : a.testBit 2 <;>
    simp [h0, h1, h2]

private theorem wp_eq (v : ℕ) : wp v = wpart v := by
  show (v &&& 1) ||| (((v >>> 1) &&& 2) ||| ((v >>> 2) &&& 4)) = _
  rw [wpart, Nat.or_assoc]

private theorem xp_eq (v : ℕ) : xp v = xpart v := by
  show ((v >>> 1) &&& 1) ||| (((v >>> 2) &&& 2) ||| ((v >>> 3) &&& 4)) = _
  rw [xpart, Nat.or_assoc]

private theorem qK_eq (u : Bool) (v : ℕ) : qK (if u then 1 else 0) v = qOf u v := by
  show ((outK (wp v) (wp v)) ^^^ ((outK (wp v) (xp v)) ^^^ ((if u then 1 else 0) * outK (xp v) (xp v))))
    = _
  rw [outK_eq, outK_eq, outK_eq, wp_eq, xp_eq, qOf, Nat.xor_assoc]
  cases u <;> simp

private theorem betaK_eq (u : Bool) (v w : ℕ) : betaK (if u then 1 else 0) v w = betaOf u v w := by
  show (qK _ (v ^^^ w)) ^^^ ((qK _ v) ^^^ (qK _ w)) = _
  rw [qK_eq, qK_eq, qK_eq, betaOf, Nat.xor_assoc]

private theorem outer_lt (a b : ℕ) : outer a b < 512 := by
  have h : ∀ (c : Prop) [Decidable c] (n : ℕ), n < 8 → (if c then n else 0) < 8 := by
    intro c _ n hn; split <;> omega
  have h1 : (if a.testBit 0 then b &&& 7 else 0) < 512 := by
    have := h (a.testBit 0 = true) (b &&& 7) (Nat.lt_of_le_of_lt Nat.and_le_right (by omega))
    omega
  have h2 : (if a.testBit 1 then (b &&& 7) <<< 3 else 0) < 512 := by
    have e : (b &&& 7) < 8 := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
    rw [Nat.shiftLeft_eq]
    split <;> omega
  have h3 : (if a.testBit 2 then (b &&& 7) <<< 6 else 0) < 512 := by
    have e : (b &&& 7) < 8 := Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
    rw [Nat.shiftLeft_eq]
    split <;> omega
  exact Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (n := 9) h1 h2) h3

private theorem qOf_lt (u : Bool) (v : ℕ) : qOf u v < 512 := by
  have h1 := outer_lt (wpart v) (wpart v)
  have h2 := outer_lt (wpart v) (xpart v)
  have h3 : (if u then outer (xpart v) (xpart v) else 0) < 512 := by
    split
    · exact outer_lt _ _
    · omega
  exact Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (n := 9) h1 h2) h3

private theorem evalV_zero (l : List ℕ) : evalV l 0 = 0 := by
  unfold evalV xorBits
  simp

private theorem evV_zero (P : ℕ) : evV P 0 = 0 := by rw [evV_eq, evalV_zero]

private theorem qOf_zero (u : Bool) : qOf u 0 = 0 := by cases u <;> decide

private theorem bOf_getD (u : Bool) (l : List ℕ) (k : ℕ) (hk : k < 9) :
    (bOf u l).getD k 0 = (fun t : ℕ × ℕ × ℕ => qOf u (evalV l t.1) ^^^ qOf u (evalV l t.2.1) ^^^ qOf u (evalV l t.2.2))
       (if k / 3 = k % 3 then (mkv (2 ^ (k / 3)) 0, 0, 0)
  else (mkv (2 ^ (k / 3)) (2 ^ (k % 3)), mkv (2 ^ (k / 3)) 0,
    if u then mkv 0 (2 ^ (k % 3)) else 0)) := by
  simp [bOf, spanW, List.getD_eq_getElem?_getD, hk]

private theorem bEntK_letN (y : ℕ) (k : ℕ → ℕ) : bEntK.letN y k = k y := by cases y <;> rfl

private theorem bEntK_unfold (u P k : ℕ) : bEntK u P k =
    Bool.rec (motive := fun _ => ℕ)
      (Nat.xor (qK u (evV P (4 ^ (k / 3) + 2 * 4 ^ (k % 3))))
        (Nat.xor (qK u (evV P (4 ^ (k / 3)))) (u * qK u (evV P (2 * 4 ^ (k % 3))))))
      (qK u (evV P (4 ^ (k / 3)))) (Nat.beq (k / 3) (k % 3)) := by
  unfold bEntK
  rw [bEntK_letN, bEntK_letN]
  rfl

private theorem mkv_a (i : ℕ) (hi : i < 3) : mkv (2 ^ i) 0 = 4 ^ i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide

private theorem mkv_b (j : ℕ) (hj : j < 3) : mkv 0 (2 ^ j) = 2 * 4 ^ j := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide

private theorem mkv_ab (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    mkv (2 ^ i) (2 ^ j) = 4 ^ i + 2 * 4 ^ j := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide

private theorem bEntK_eq (u : Bool) (P k : ℕ) (hk : k < 9) :
    bEntK (if u then 1 else 0) P k = (bOf u (unpack6 P)).getD k 0 := by
  rw [bEntK_unfold, bOf_getD u _ k hk]
  have hi : k / 3 < 3 := by omega
  have hj : k % 3 < 3 := by omega
  generalize k / 3 = i at *
  generalize k % 3 = j at *
  by_cases hij : i = j
  · subst hij
    simp only [Nat.beq_refl, if_true, mkv_a i hi, ← evV_eq, qK_eq, evalV_zero, qOf_zero,
      Nat.xor_zero]
  · have hb : Nat.beq i j = false := Bool.eq_false_iff.2 fun h => hij (Nat.eq_of_beq_eq_true h)
    rw [hb]
    simp only [hij, if_false, mkv_a i hi, mkv_ab i j hi hj, mkv_b j hj, ← evV_eq, qK_eq, evalV_zero,
      qOf_zero, Nat.xor_zero, evV_zero]
    cases u <;> simp [Nat.xor_assoc, evV_zero, qOf_zero]

private theorem bOf_getD_lt (u : Bool) (l : List ℕ) (k : ℕ) (hk : k < 9) : (bOf u l).getD k 0 < 512 := by
  rw [bOf_getD u l k hk]
  exact Nat.xor_lt_two_pow (n := 9) (Nat.xor_lt_two_pow (n := 9) (qOf_lt _ _) (qOf_lt _ _))
    (qOf_lt _ _)

private theorem fld9_eq' (P i : ℕ) : fld9 P i = P / 2 ^ (9 * i) % 2 ^ 9 := by
  rw [fld9_eq, Nat.pow_mul]; rfl

private theorem evE_bOfK (u : Bool) (P e : ℕ) :
    evE (bOfK (if u then 1 else 0) P) e = evalE (bOf u (unpack6 P)) e := by
  have hlt : ∀ k, k < 9 → bEntK (if u then 1 else 0) P k < 2 ^ 9 := fun k hk => by
    rw [bEntK_eq u P k hk]; exact bOf_getD_lt u _ k hk
  have h := (pkW_spec 9 (fun k => bEntK (if u then 1 else 0) P k) 9 hlt).2
  rw [evE_xor]
  refine xorBits_congr (fun j hj => ?_) e
  rw [fld9_eq', ← bEntK_eq u P j hj]
  exact h j hj

private theorem cntK_eq (N : ℕ) (f : ℕ → Bool) : cntK N f = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ n ih =>
    show Nat.add (cntK n f) (Bool.rec 0 1 (f n)) = _
    rw [List.range_succ, List.filter_append, List.length_append, ← ih]
    cases h : f n <;> simp [h]

private theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

private theorem notB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

private theorem anyN_iff {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i, i < m ∧ f i = true := by
  induction m with
  | zero => exact ⟨fun h => absurd (h : false = true) Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
  | succ m ih =>
    change orB (f m) (anyN m f) = true ↔ _
    rw [orB_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

private theorem memK_iff' {x : ℕ} {L : List ℕ} : memK x L = true ↔ x ∈ L := by
  induction L with
  | nil =>
    refine ⟨fun h => ?_, fun h => absurd h List.not_mem_nil⟩
    change false = true at h
    exact absurd h (by decide)
  | cons y t ih =>
    change orB (Nat.beq y x) (memK x t) = true ↔ _
    rw [List.mem_cons, ← ih]
    cases h : Nat.beq y x
    · have hne : x ≠ y := fun e => Nat.ne_of_beq_eq_false h e.symm
      change memK x t = true ↔ _
      simp [hne]
    · have he : x = y := (Nat.eq_of_beq_eq_true h).symm
      change true = true ↔ _
      simp [he]

private theorem nodupK_sound' {L : List ℕ} (h : nodupK L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x t ih =>
    change andB (notB (memK x t)) (nodupK t) = true at h
    rw [andB_iff, notB_iff] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, ih h.2⟩
    rw [← memK_iff', h.1] at hx
    exact absurd hx (by decide)

private theorem lenK_eq' (L : List ℕ) : lenK L = L.length := by
  induction L with
  | nil => rfl
  | cons _ t ih =>
    change Nat.succ (lenK t) = _
    rw [ih]
    rfl

private theorem elsK_eq (P : ℕ) (ws : List (List ℕ)) :
    elsK P ws = ws.map fun x => wordK P x idK := by
  induction ws with
  | nil => rfl
  | cons x t ih =>
    change List.cons _ (elsK P t) = _
    rw [ih]
    rfl

private theorem codeT_unpack6_inj {x y : ℕ} (hx : x < 2 ^ 36) (hy : y < 2 ^ 36)
    (h : codeT (unpack6 x) = codeT (unpack6 y)) : x = y := by
  have key : ∀ z : ℕ, z < 2 ^ 36 → unpack6 z = [z % 64, z / 64 % 64, z / 4096 % 64,
      z / 262144 % 64, z / 16777216 % 64, z / 1073741824 % 64] := fun z hz => by
    show [z / 64 ^ 0 % 64, z / 64 ^ 1 % 64, z / 64 ^ 2 % 64, z / 64 ^ 3 % 64, z / 64 ^ 4 % 64,
      z / 64 ^ 5 % 64] = _
    simp only [Nat.pow_zero, Nat.pow_one, Nat.div_one]
    rfl
  have e : ∀ z : ℕ, z < 2 ^ 36 → z = z % 64 + 64 * (z / 64 % 64) + 4096 * (z / 4096 % 64) +
      262144 * (z / 262144 % 64) + 16777216 * (z / 16777216 % 64) +
      1073741824 * (z / 1073741824 % 64) := fun z hz => by omega
  rw [key x hx, key y hy] at h
  simp only [codeT, List.foldl_cons, List.foldl_nil] at h
  have hb : ∀ z : ℕ, z % 64 < 64 ∧ z / 64 % 64 < 64 ∧ z / 4096 % 64 < 64 ∧ z / 262144 % 64 < 64 ∧
      z / 16777216 % 64 < 64 ∧ z / 1073741824 % 64 < 64 := fun z => by omega
  have hbx := hb x
  have hby := hb y
  have hx6 := e x hx
  have hy6 := e y hy
  generalize x % 64 = a0 at *
  generalize x / 64 % 64 = a1 at *
  generalize x / 4096 % 64 = a2 at *
  generalize x / 262144 % 64 = a3 at *
  generalize x / 16777216 % 64 = a4 at *
  generalize x / 1073741824 % 64 = a5 at *
  generalize y % 64 = b0 at *
  generalize y / 64 % 64 = b1 at *
  generalize y / 4096 % 64 = b2 at *
  generalize y / 262144 % 64 = b3 at *
  generalize y / 16777216 % 64 = b4 at *
  generalize y / 1073741824 % 64 = b5 at *
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5⟩ := hbx
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5⟩ := hby
  have hd : a5 = b5 ∧ a4 = b4 ∧ a3 = b3 ∧ a2 = b2 ∧ a1 = b1 ∧ a0 = b0 := by
    clear hx6 hy6 hx hy
    have e5 : a5 = b5 := by omega
    subst e5
    have e4 : a4 = b4 := by omega
    subst e4
    have e3 : a3 = b3 := by omega
    subst e3
    have e2 : a2 = b2 := by omega
    subst e2
    have e1 : a1 = b1 := by omega
    subst e1
    have e0 : a0 = b0 := by omega
    exact ⟨rfl, rfl, rfl, rfl, rfl, e0⟩
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hd
  omega

theorem certK_sound' (u : Bool) {P : ℕ} {ws : List (List ℕ)} {v w : ℕ}
    (hws : ∀ x ∈ ws, ∀ a ∈ x, a < 4)
    (h : certK (if u then 1 else 0) P ws v w = true) :
    validCert u (unpack6 P) (ws, v, w) = true := by
  unfold certK at h
  rw [letB_eq] at h
  simp only [andB_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  simp only [validCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem,
    List.all_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_range, List.any_eq_true]
  have hE : elsK P ws = ws.map fun x => wordK P x idK := elsK_eq P ws
  have hmap : ws.map (evalW (unpack6 P)) = (elsK P ws).map unpack6 := by
    rw [hE, List.map_map]
    exact List.map_congr_left fun x hx => (unpack6_wordK_id P x (hws x hx)).symm
  have hlt : ∀ x ∈ elsK P ws, x < 2 ^ 36 := by
    intro x hx
    rw [hE] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact wordK_lt P y idK (by decide)
  have hlen : (ws.map (evalW (unpack6 P))).length = lenK (elsK P ws) := by
    rw [lenK_eq', hmap, List.length_map]
  have hcode : ∀ x ∈ elsK P ws, ∀ y ∈ elsK P ws, codeT (unpack6 x) = codeT (unpack6 y) → x = y :=
    fun x hx y hy hxy => codeT_unpack6_inj (hlt x hx) (hlt y hy) hxy
  have hfix : cntK 64 (fun x => eqN (evV P x) x) = (fixV (unpack6 P)).length := by
    rw [cntK_eq]
    unfold fixV
    refine congrArg List.length (List.filter_congr fun x _ => ?_)
    rw [evV_eq]
    exact eqN_eq _ _
  have hfe : cntK 512 (fun e => eqN (evE (bOfK (if u then 1 else 0) P) e) e) =
      ((List.range 512).filter fun e => evalE (bOf u (unpack6 P)) e == e).length := by
    rw [cntK_eq]
    refine congrArg List.length (List.filter_congr fun x _ => ?_)
    rw [evE_bOfK]
    exact eqN_eq _ _
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hlen]
    simpa only [Nat.blt_eq] using h1
  · obtain ⟨k, hk, hk2⟩ := anyN_iff.1 h2
    exact ⟨k, hk, by rw [hlen]; exact Nat.eq_of_beq_eq_true hk2⟩
  · rw [hmap, List.map_map]
    exact (nodupK_sound' h3).map_on hcode
  · rw [hmap, List.map_map]
    exact List.mem_map.2 ⟨idK, memK_iff'.1 h4, by
      show codeT (unpack6 idK) = _
      rw [unpack6_idK]⟩
  · rw [hmap, List.map_map]
    exact List.mem_map.2 ⟨P, memK_iff'.1 h5, rfl⟩
  · intro a ha b hb
    rw [hmap] at ha hb ⊢
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.1 hb
    have h6a : allL (elsK P ws) (fun b => memK (compK a0 b) (elsK P ws)) = true :=
      allL_iff'.1 h6 a0 ha0
    have hm : memK (compK a0 b0) (elsK P ws) = true := allL_iff'.1 h6a b0 hb0
    rw [← unpack6_compK, List.map_map]
    exact List.mem_map.2 ⟨compK a0 b0, memK_iff'.1 hm, rfl⟩
  · intro a ha
    rw [hmap] at ha
    obtain ⟨a0, ha0, rfl⟩ := List.mem_map.1 ha
    have e := congrArg unpack6 (Nat.eq_of_beq_eq_true (allL_iff'.1 h7 a0 ha0))
    rw [unpack6_compK, unpack6_compK] at e
    exact e
  · rw [hfix, hfe] at h8
    rw [hlen]
    exact Nat.le_of_ble_eq_true h8
  · simpa only [Nat.blt_eq] using h9
  · simpa only [Nat.blt_eq] using h10
  · rw [← evV_eq]
    exact Nat.eq_of_beq_eq_true h11
  · rw [← evV_eq]
    exact Nat.eq_of_beq_eq_true h12
  · intro e he hbe
    refine (Bool.eq_false_iff.1 (notB_iff.1 h13)) (anyN_iff.2 ⟨e, he, ?_⟩)
    have h' : Nat.xor (evE (bOfK (if u then 1 else 0) P) e) e =
        betaK (if u then 1 else 0) v w := by
      rw [evE_bOfK, betaK_eq]
      exact hbe
    show Nat.beq _ _ = true
    rw [h']
    exact Nat.beq_refl _

end CFSG.KC.Misc.Oq

end
