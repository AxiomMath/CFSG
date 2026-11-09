module

public import CFSG.Certificates.Kernel.Common.LabF

public section

namespace CFSG.KC.LabZ

open CFSG.KC CFSG.KC.LceS CFSG.KC.Loop CFSG.KC.LabF

@[expose] noncomputable def addZ (d dir a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (Nat.sub a (Nat.land d (nat_lit 15)))
      (Nat.add a (Nat.land d (nat_lit 15))) (Nat.beq dir (nat_lit 1)))
    (Bool.rec (motive := fun _ => Nat) (Nat.add a (Nat.land d (nat_lit 15)))
      (Nat.sub a (Nat.land d (nat_lit 15))) (Nat.beq dir (nat_lit 1)))
    (Nat.blt d (nat_lit 16))

@[expose] noncomputable def labGoZ (CD : Nat → Nat) (di ft n : Nat) (k : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun k ih R acc => Bool.rec (motive := fun _ => Nat)
      ((fun e => strictN (addZ (CD (Nat.shiftRight e (nat_lit 1))) (Nat.land e (nat_lit 1)) acc)
          (ih (Nat.shiftRight R (nat_lit 32))))
        (Nat.land R (nat_lit 4294967295)))
      (strictN (addZ di (nat_lit 0) acc) (ih R))
      (Nat.beq (Nat.sub n (Nat.succ k)) ft)) k

@[expose] noncomputable def targetZ (w h : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 4294967296)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 4294967297) (Nat.beq h (nat_lit 0)))
    (Nat.beq (wKind w) (nat_lit 3))

@[expose] noncomputable def labWalkZ (CD : Nat → Nat) (i J w h : Nat) : Bool :=
  Nat.beq (labGoZ CD (CD i) (Nat.land (Nat.shiftRight J (nat_lit 37)) (nat_lit 65535)) (wLen w)
      (wLen w) (Nat.shiftRight J (nat_lit 53)) (nat_lit 4294967296))
    (targetZ w h)

@[expose] noncomputable def labStepZ (CD : Nat → Nat) (Hs J S w : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (Nat.beq (Nat.land (CD (Nat.sub S (nat_lit 1))) (nat_lit 15)) (nat_lit 0)))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ S)
        (labWalkZ CD (Nat.sub S (nat_lit 1)) J w
          (hint Hs (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.blt (nat_lit 0) S)

@[expose] noncomputable def labChunkZ (WT CD : Nat → Nat) (Hs C S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ S => S)
    (fun _ ih J S => Bool.rec (motive := fun _ => Nat)
      (strictN (labStepZ CD Hs J S (nat_lit 0)) (ih (Nat.shiftRight J (nat_lit 1))))
      (strictN (strictN (Nat.land (Nat.shiftRight J (nat_lit 1)) (nat_lit 65535)) WT) (fun w =>
        strictN (labStepZ CD Hs J S w) (ih (Nat.shiftRight J (jLen J w)))))
      (Nat.beq (Nat.land J (nat_lit 1)) (nat_lit 1)))
    (Nat.land C (nat_lit 255)) (Nat.shiftRight C (nat_lit 8)) S

@[expose] noncomputable def runLabC (WT CD : Nat → Nat) (Hs : Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun C _ ih S => strictN (labChunkZ WT CD Hs C S) ih) Cs

@[expose] def rep (b : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => rep b m * 256 + b

@[expose] noncomputable def pwN (A : Nat) : Nat :=
  if 4294967296 ≤ A then mkK (A - 4294967296) (rep 1 (A - 4294967296))
  else mkK (4294967296 - A) (rep 2 (4294967296 - A))

@[expose] def pcode (d : Nat) : Nat := if d < 16 then 4294967296 + d % 16 else 4294967296 - d % 16

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem land_mod (x n m : Nat) (h : m = 2 ^ n - 1) : Nat.land x m = x % 2 ^ n := by
  subst h
  exact Nat.and_two_pow_sub_one_eq_mod x n

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp e) h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.blt_eq.mpr h

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem nbeq_true {a b : Nat} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

theorem nbeq_ne {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem addZ_def (d dir a : Nat) : addZ d dir a =
    Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (a - d % 16) (a + d % 16) (Nat.beq dir 1))
      (Bool.rec (motive := fun _ => Nat) (a + d % 16) (a - d % 16) (Nat.beq dir 1))
      (Nat.blt d 16) := by
  unfold addZ
  rw [show Nat.land d (nat_lit 15) = d % 16 from land_mod d 4 15 rfl]
  rfl

theorem lpush_def (K x : Nat) : lpush K x =
    Bool.rec (motive := fun _ => Nat) (mkK (kCnt K + 1) (kStk K * 256 + (x + 1)))
      (mkK (kCnt K - 1) (Nat.shiftRight (kStk K) 8))
      (andB (Nat.blt 0 (kCnt K)) (Nat.beq (Nat.land (kStk K) 255) (Nat.xor x 1 + 1))) := rfl

theorem pushFwd_def (L acc : Nat) : pushFwd L acc =
    Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
      (fun k ih a => strictN (lpush a (kByte L k - 1)) ih) (kCnt L) acc := rfl

theorem pushInv_def (L acc : Nat) : pushInv L acc =
    Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
      (fun k ih a => strictN (lpush a (Nat.xor (kByte L (kCnt L - 1 - k) - 1) 1)) ih) (kCnt L)
      acc :=
  rfl

theorem pushLab_def (L dir acc : Nat) : pushLab L dir acc =
    Bool.rec (motive := fun _ => Nat) (pushFwd L acc) (pushInv L acc) (Nat.beq dir 1) := rfl

theorem labGo_succ (LB : Nat → Nat) (Li ft n k R acc : Nat) : labGo LB Li ft n (k + 1) R acc =
    Bool.rec (motive := fun _ => Nat)
      (strictN (pushLab (LB (Nat.shiftRight (Nat.land R 4294967295) 1))
        (Nat.land (Nat.land R 4294967295) 1) acc) (labGo LB Li ft n k (Nat.shiftRight R 32)))
      (strictN (pushFwd Li acc) (labGo LB Li ft n k R))
      (Nat.beq (n - (k + 1)) ft) := rfl

theorem labGoZ_succ (CD : Nat → Nat) (di ft n k R acc : Nat) : labGoZ CD di ft n (k + 1) R acc =
    Bool.rec (motive := fun _ => Nat)
      (strictN (addZ (CD (Nat.shiftRight (Nat.land R 4294967295) 1))
        (Nat.land (Nat.land R 4294967295) 1) acc) (labGoZ CD di ft n k (Nat.shiftRight R 32)))
      (strictN (addZ di 0 acc) (labGoZ CD di ft n k R))
      (Nat.beq (n - (k + 1)) ft) := rfl

theorem labWalk_def (LB : Nat → Nat) (i J w h : Nat) : labWalk LB i J w h =
    Nat.beq (labGo LB (LB i) (Nat.land (Nat.shiftRight J 37) 65535) (wLen w) (wLen w)
      (Nat.shiftRight J 53) 0) (target w h) := rfl

theorem labWalkZ_def (CD : Nat → Nat) (i J w h : Nat) : labWalkZ CD i J w h =
    Nat.beq (labGoZ CD (CD i) (Nat.land (Nat.shiftRight J 37) 65535) (wLen w) (wLen w)
      (Nat.shiftRight J 53) 4294967296) (targetZ w h) := rfl

theorem target_def (w h : Nat) : target w h =
    Bool.rec (motive := fun _ => Nat) 0 (mkK 1 (2 * h + 1)) (Nat.beq (wKind w) 3) := rfl

theorem targetZ_def (w h : Nat) : targetZ w h =
    Bool.rec (motive := fun _ => Nat) 4294967296
      (Bool.rec (motive := fun _ => Nat) 0 4294967297 (Nat.beq h 0)) (Nat.beq (wKind w) 3) := rfl

theorem labStep_def (LB : Nat → Nat) (Hs J S w : Nat) : labStep LB Hs J S w =
    Bool.rec (motive := fun _ => Nat) 0
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 0 (S + 1) (Nat.beq (LB (S - 1)) 0))
        (Bool.rec (motive := fun _ => Nat) 0 (S + 1)
          (labWalk LB (S - 1) J w (hint Hs (Nat.land (Nat.shiftRight J 1) 65535))))
        (Nat.beq (Nat.land J 1) 1))
      (Nat.blt 0 S) := rfl

theorem labStepZ_def (CD : Nat → Nat) (Hs J S w : Nat) : labStepZ CD Hs J S w =
    Bool.rec (motive := fun _ => Nat) 0
      (Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) 0 (S + 1) (Nat.beq (Nat.land (CD (S - 1)) 15) 0))
        (Bool.rec (motive := fun _ => Nat) 0 (S + 1)
          (labWalkZ CD (S - 1) J w (hint Hs (Nat.land (Nat.shiftRight J 1) 65535))))
        (Nat.beq (Nat.land J 1) 1))
      (Nat.blt 0 S) := rfl

theorem mkK_eq {c : Nat} (s : Nat) (hc : c < 16777216) : mkK c s = s * 16777216 + c := by
  unfold mkK
  have e := Nat.shiftLeft_add_eq_or_of_lt (i := 24) (b := c) hc s
  have e2 : Nat.lor c (Nat.shiftLeft s 24) = s <<< 24 ||| c := Nat.or_comm c (s <<< 24)
  rw [e2, ← e, Nat.shiftLeft_eq]

theorem kCnt_mkK {c : Nat} (s : Nat) (hc : c < 16777216) : kCnt (mkK c s) = c := by
  unfold kCnt
  rw [mkK_eq s hc, land_mod _ 24 _ rfl]
  change (s * 16777216 + c) % 16777216 = c
  omega

theorem kStk_mkK {c : Nat} (s : Nat) (hc : c < 16777216) : kStk (mkK c s) = s := by
  unfold kStk
  rw [mkK_eq s hc]
  change (s * 16777216 + c) >>> 24 = s
  rw [Nat.shiftRight_eq_div_pow]
  change (s * 16777216 + c) / 16777216 = s
  omega

theorem rep_succ (b m : Nat) : rep b (m + 1) = rep b m * 256 + b := rfl

theorem rep_mod {b : Nat} (hb : b < 256) : ∀ m, 0 < m → rep b m % 256 = b
  | m + 1, _ => by
    simp only [rep]
    omega

theorem rep_div {b : Nat} (hb : b < 256) (m : Nat) : rep b (m + 1) / 256 = rep b m := by
  simp only [rep]
  omega

theorem rep_shr {b : Nat} (hb : b < 256) (m : Nat) : ∀ i ≤ m, rep b m >>> (8 * i) = rep b (m - i)
  | 0, _ => by simp
  | i + 1, hi => by
    rw [show 8 * (i + 1) = 8 * i + 8 by omega, Nat.shiftRight_add, rep_shr hb m i (by omega),
      show m - i = (m - (i + 1)) + 1 by omega, Nat.shiftRight_eq_div_pow]
    exact rep_div hb _

theorem rep_shr8 {b : Nat} (hb : b < 256) {m : Nat} (hm : 0 < m) :
    Nat.shiftRight (rep b m) 8 = rep b (m - 1) := by
  have := rep_shr hb m 1 hm
  exact this

theorem kByte_rep {b m : Nat} (hb : b < 256) (hm : m < 16777216) {i : Nat} (hi : i < m) :
    kByte (mkK m (rep b m)) i = b := by
  unfold kByte
  rw [kStk_mkK _ hm, land_mod _ 8 _ rfl]
  change rep b m >>> (8 * i) % 256 = b
  rw [rep_shr hb m i (by omega)]
  exact rep_mod hb _ (by omega)

theorem pwN_hi {A : Nat} (h : 4294967296 ≤ A) :
    pwN A = mkK (A - 4294967296) (rep 1 (A - 4294967296)) := by
  simp only [pwN, if_pos h]

theorem pwN_lo {A : Nat} (h : A < 4294967296) :
    pwN A = mkK (4294967296 - A) (rep 2 (4294967296 - A)) := by
  simp only [pwN, if_neg (Nat.not_le.2 h)]

theorem top_byte {b m : Nat} (hb : b = 1 ∨ b = 2) (x : Nat) (hx : x < 2) :
    Nat.beq (Nat.land (rep b m) 255) (Nat.xor x 1 + 1) =
      (decide (0 < m) && decide (b + x = 2)) := by
  rw [land_mod _ 8 _ rfl, show (2 : Nat) ^ 8 = 256 from rfl]
  rcases m with _ | m
  · rcases hb with rfl | rfl <;> (obtain rfl | rfl : x = 0 ∨ x = 1 := by omega) <;> rfl
  · rw [rep_mod (by omega) _ (by omega)]
    rcases hb with rfl | rfl <;> (obtain rfl | rfl : x = 0 ∨ x = 1 := by omega) <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> cases b <;> rfl

theorem blt0 (m : Nat) : Nat.blt 0 m = decide (0 < m) := by
  rcases m with _ | m
  · rfl
  · rw [blt_true (Nat.succ_pos m)]
    exact (decide_eq_true (Nat.succ_pos m)).symm

theorem lpush_rep {b m : Nat} (hb : b = 1 ∨ b = 2) (x : Nat) (hx : x < 2) (hm : m + 1 < 16777216) :
    lpush (mkK m (rep b m)) x =
      if 0 < m ∧ b + x = 2 then mkK (m - 1) (rep b (m - 1))
      else mkK (m + 1) (rep b m * 256 + (x + 1)) := by
  rw [lpush_def, kCnt_mkK _ (by omega), kStk_mkK _ (by omega), top_byte hb x hx, blt0, andB_eq]
  by_cases hc : 0 < m ∧ b + x = 2
  · rw [if_pos hc]
    have e : (decide (0 < m) && (decide (0 < m) && decide (b + x = 2))) = true := by
      simp [hc.1, hc.2]
    rw [e]
    dsimp only
    rw [rep_shr8 (by omega) hc.1]
  · rw [if_neg hc]
    have e : (decide (0 < m) && (decide (0 < m) && decide (b + x = 2))) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    rw [e]

theorem lpush_pw0 {A : Nat} (h1 : 4278190082 ≤ A) (h2 : A ≤ 4311744510) :
    lpush (pwN A) 0 = pwN (A + 1) := by
  by_cases hA : 4294967296 ≤ A
  · rw [pwN_hi hA, lpush_rep (Or.inl rfl) 0 (by omega) (by omega), if_neg (by omega),
      pwN_hi (by omega),
      show A + 1 - 4294967296 = (A - 4294967296) + 1 by omega, rep_succ, Nat.zero_add]
  · rw [pwN_lo (by omega), lpush_rep (Or.inr rfl) 0 (by omega) (by omega), if_pos (by omega)]
    by_cases hA1 : A + 1 = 4294967296
    · rw [pwN_hi (by omega), show 4294967296 - A - 1 = 0 by omega, hA1, Nat.sub_self]
      rfl
    · rw [pwN_lo (by omega), show 4294967296 - (A + 1) = 4294967296 - A - 1 by omega]

theorem lpush_pw1 {A : Nat} (h1 : 4278190082 ≤ A) (h2 : A ≤ 4311744510) :
    lpush (pwN A) 1 = pwN (A - 1) := by
  by_cases hA : 4294967296 < A
  · rw [pwN_hi (by omega), lpush_rep (Or.inl rfl) 1 (by omega) (by omega), if_pos (by omega),
      pwN_hi (by omega), show A - 1 - 4294967296 = A - 4294967296 - 1 by omega]
  · by_cases hA0 : A = 4294967296
    · subst hA0
      rw [pwN_hi (Nat.le_refl _), Nat.sub_self, lpush_rep (Or.inl rfl) 1 (by omega) (by omega),
        if_neg (by omega), pwN_lo (by omega), show 4294967296 - (4294967296 - 1) = 1 by omega]
      rfl
    · rw [pwN_lo (by omega), lpush_rep (Or.inr rfl) 1 (by omega) (by omega), if_neg (by omega),
        pwN_lo (by omega), show 4294967296 - (A - 1) = (4294967296 - A) + 1 by omega, rep_succ,
        show (1 : Nat) + 1 = 2 from rfl]

theorem iter_pw (g : Nat → Nat) (ℓ : Nat) (hℓ : ℓ = 0 ∨ ℓ = 1) :
    ∀ m, (∀ k < m, g k = ℓ) → ∀ A, 4278190082 + m ≤ A → A + m ≤ 4311744510 →
      Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
        (fun k ih a => strictN (lpush a (g k)) ih) m (pwN A) =
        pwN (if ℓ = 0 then A + m else A - m)
  | 0, _, A, _, _ => by
    rw [Nat.add_zero, Nat.sub_zero, ite_self]
    rfl
  | m + 1, hg, A, h1, h2 => by
    have st : Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
        (fun k ih a => strictN (lpush a (g k)) ih) (m + 1) (pwN A) =
        Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
        (fun k ih a => strictN (lpush a (g k)) ih) m (lpush (pwN A) (g m)) :=
      strictN_eq _ _
    rw [st, hg m (by omega)]
    rcases hℓ with rfl | rfl
    · rw [lpush_pw0 (by omega) (by omega),
        iter_pw g 0 (Or.inl rfl) m (fun k hk => hg k (by omega)) (A + 1) (by omega) (by omega)]
      simp only [if_true]
      congr 1
      omega
    · rw [lpush_pw1 (by omega) (by omega),
        iter_pw g 1 (Or.inr rfl) m (fun k hk => hg k (by omega)) (A - 1) (by omega) (by omega)]
      simp only [Nat.one_ne_zero, if_false]
      congr 1
      omega

theorem addZ_bd (d dir : Nat) {a : Nat} (ha : 15 ≤ a) :
    a - 15 ≤ addZ d dir a ∧ addZ d dir a ≤ a + 15 := by
  have h15 : d % 16 < 16 := Nat.mod_lt _ (by omega)
  rw [addZ_def]
  cases Nat.blt d 16 <;> cases Nat.beq dir 1 <;> dsimp only <;> omega

theorem pwN_pcode (d : Nat) :
    (d < 16 ∨ d % 16 = 0 → pwN (pcode d) = mkK (d % 16) (rep 1 (d % 16))) ∧
    (¬ d < 16 → 0 < d % 16 → pwN (pcode d) = mkK (d % 16) (rep 2 (d % 16))) := by
  have hdm : d % 16 < 16 := Nat.mod_lt _ (by omega)
  constructor
  · intro h
    by_cases hd : d < 16
    · rw [pwN_hi (by simp [pcode, hd]), show pcode d = 4294967296 + d % 16 by simp [pcode, hd],
        show 4294967296 + d % 16 - 4294967296 = d % 16 by omega]
    · have h0 : d % 16 = 0 := h.resolve_left hd
      have e : pcode d = 4294967296 := by simp [pcode, hd, h0]
      rw [e, pwN_hi (Nat.le_refl _), h0]
  · intro hd h0
    have e : pcode d = 4294967296 - d % 16 := by simp [pcode, hd]
    rw [pwN_lo (by omega), e, show 4294967296 - (4294967296 - d % 16) = d % 16 by omega]

theorem pushFwd_pw {b j : Nat} (hb : b = 1 ∨ b = 2) (hj : j < 16) {A : Nat} (h1 : 4278190112 ≤ A)
    (h2 : A ≤ 4311744480) :
    pushFwd (mkK j (rep b j)) (pwN A) = pwN (if b = 1 then A + j else A - j) := by
  rw [pushFwd_def, kCnt_mkK _ (by omega)]
  refine (iter_pw (fun k => kByte (mkK j (rep b j)) k - 1) (b - 1) (by omega) j
    (fun k hk => by
      change kByte (mkK j (rep b j)) k - 1 = b - 1
      rw [kByte_rep (by omega) (by omega) hk]) A (by omega) (by omega)).trans ?_
  rcases hb with rfl | rfl <;> simp

theorem pushInv_pw {b j : Nat} (hb : b = 1 ∨ b = 2) (hj : j < 16) {A : Nat} (h1 : 4278190112 ≤ A)
    (h2 : A ≤ 4311744480) :
    pushInv (mkK j (rep b j)) (pwN A) = pwN (if b = 1 then A - j else A + j) := by
  rw [pushInv_def, kCnt_mkK _ (by omega)]
  refine (iter_pw (fun k => Nat.xor (kByte (mkK j (rep b j)) (j - 1 - k) - 1) 1) (2 - b)
    (by omega) j
    (fun k hk => by
      change Nat.xor (kByte (mkK j (rep b j)) (j - 1 - k) - 1) 1 = 2 - b
      rw [kByte_rep (by omega) (by omega) (by omega)]
      rcases hb with rfl | rfl <;> rfl) A (by omega) (by omega)).trans ?_
  rcases hb with rfl | rfl <;> simp

theorem pushLab_code (d dir : Nat) {A : Nat} (h1 : 4278190112 ≤ A) (h2 : A ≤ 4311744480) :
    pushLab (pwN (pcode d)) dir (pwN A) = pwN (addZ d dir A) := by
  have hdm : d % 16 < 16 := Nat.mod_lt _ (by omega)
  obtain ⟨p1, p2⟩ := pwN_pcode d
  rw [pushLab_def, addZ_def]
  by_cases hd : d < 16
  · rw [p1 (Or.inl hd), blt_true hd]
    cases Nat.beq dir 1
    · dsimp only
      rw [pushFwd_pw (Or.inl rfl) hdm h1 h2]
      simp
    · dsimp only
      rw [pushInv_pw (Or.inl rfl) hdm h1 h2]
      simp
  · rw [blt_false hd]
    rcases Nat.eq_zero_or_pos (d % 16) with h0 | h0
    · rw [p1 (Or.inr h0), h0]
      cases Nat.beq dir 1
      · dsimp only
        rw [pushFwd_pw (Or.inl rfl) (by omega) h1 h2]
        simp
      · dsimp only
        rw [pushInv_pw (Or.inl rfl) (by omega) h1 h2]
        simp
    · rw [p2 hd h0]
      cases Nat.beq dir 1
      · dsimp only
        rw [pushFwd_pw (Or.inr rfl) hdm h1 h2]
        simp
      · dsimp only
        rw [pushInv_pw (Or.inr rfl) hdm h1 h2]
        simp

theorem pwN_shape {A : Nat} (h1 : 4278190112 ≤ A) (h2 : A ≤ 4311744480) :
    ∃ b j, (b = 1 ∨ b = 2) ∧ j < 16777216 ∧ pwN A = mkK j (rep b j) ∧
      (b = 1 → A = 4294967296 + j) ∧ (b = 2 → A = 4294967296 - j ∧ 0 < j) := by
  by_cases hA : 4294967296 ≤ A
  · exact ⟨1, A - 4294967296, Or.inl rfl, by omega, pwN_hi hA, fun _ => by omega,
      fun h => absurd h (by omega)⟩
  · exact ⟨2, 4294967296 - A, Or.inr rfl, by omega, pwN_lo (by omega),
      fun h => absurd h (by omega), fun _ => ⟨by omega, by omega⟩⟩

theorem pwN_inj {A B : Nat} (h1 : 4278190112 ≤ A) (h2 : A ≤ 4311744480) (h3 : 4278190112 ≤ B)
    (h4 : B ≤ 4311744480) (e : pwN A = pwN B) : A = B := by
  obtain ⟨b, j, hb, hj, eA, a1, a2⟩ := pwN_shape h1 h2
  obtain ⟨c, i, hc, hi, eB, b1, b2⟩ := pwN_shape h3 h4
  rw [eA, eB] at e
  have ej : j = i := by rw [← kCnt_mkK (rep b j) hj, e, kCnt_mkK _ hi]
  subst ej
  have es : rep b j = rep c j := by rw [← kStk_mkK (rep b j) hj, e, kStk_mkK _ hi]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
    · rw [a1 rfl, b1 rfl]
    · exact absurd (b2 rfl).2 (by omega)
    · exact absurd (a2 rfl).2 (by omega)
    · exact absurd (a2 rfl).2 (by omega)
  · have m1 := rep_mod (b := b) (by omega) j h0
    have m2 := rep_mod (b := c) (by omega) j h0
    rw [es] at m1
    have : b = c := by omega
    subst this
    rcases hb with rfl | rfl
    · rw [a1 rfl, b1 rfl]
    · rw [(a2 rfl).1, (b2 rfl).1]

theorem beq_pwN {A B : Nat} (h1 : 4278190112 ≤ A) (h2 : A ≤ 4311744480) (h3 : 4278190112 ≤ B)
    (h4 : B ≤ 4311744480) : Nat.beq (pwN A) (pwN B) = Nat.beq A B := by
  by_cases e : A = B
  · rw [e, Nat.beq_refl, Nat.beq_refl]
  · rw [nbeq_false e, nbeq_false (fun h => e (pwN_inj h1 h2 h3 h4 h))]

theorem zero_eq_pwN : (0 : Nat) = pwN 4294967296 := by
  rw [pwN_hi (Nat.le_refl _), mkK_eq _ (by omega)]
  rfl

theorem pwN_code_zero (d : Nat) : Nat.beq (pwN (pcode d)) 0 = Nat.beq (Nat.land d 15) 0 := by
  have hm : Nat.land d 15 = d % 16 := land_mod d 4 15 rfl
  have hdm : d % 16 < 16 := Nat.mod_lt _ (by omega)
  obtain ⟨p1, p2⟩ := pwN_pcode d
  rw [hm]
  rcases Nat.eq_zero_or_pos (d % 16) with h0 | h0
  · rw [p1 (Or.inr h0), h0]
    rfl
  · have e : pwN (pcode d) = mkK (d % 16) (rep (if d < 16 then 1 else 2) (d % 16)) := by
      by_cases hd : d < 16
      · rw [p1 (Or.inl hd), if_pos hd]
      · rw [p2 hd h0, if_neg hd]
    rw [e, mkK_eq _ (by omega), nbeq_false (by omega), nbeq_false (by omega)]

theorem mkK_ne {j b : Nat} (hj : j < 16777216) (c s : Nat) (hc : c < 16777216)
    (h : j ≠ c ∨ rep b j ≠ s) : mkK j (rep b j) ≠ mkK c s := by
  intro e
  rcases h with h | h
  · exact h (by rw [← kCnt_mkK (rep b j) hj, e, kCnt_mkK s hc])
  · exact h (by rw [← kStk_mkK (rep b j) hj, e, kStk_mkK s hc])

section Run

variable {LB CD : Nat → Nat} (hLB : ∀ i, LB i = pwN (pcode (CD i)))

include hLB

theorem labGo_eq (di ft n : Nat) : ∀ k R A, 4278190112 + 15 * k ≤ A → A + 15 * k ≤ 4311744480 →
    labGo LB (pwN (pcode di)) ft n k R (pwN A) = pwN (labGoZ CD di ft n k R A) ∧
      A ≤ labGoZ CD di ft n k R A + 15 * k ∧ labGoZ CD di ft n k R A ≤ A + 15 * k
  | 0, R, A, _, _ => ⟨rfl, by change A ≤ A + 15 * 0; omega, by change A ≤ A + 15 * 0; omega⟩
  | k + 1, R, A, h1, h2 => by
    rw [labGo_succ, labGoZ_succ]
    cases Nat.beq (n - (k + 1)) ft
    · dsimp only
      rw [strictN_eq, strictN_eq, hLB, pushLab_code _ _ (by omega) (by omega)]
      have hb := addZ_bd (CD (Nat.shiftRight (Nat.land R 4294967295) 1))
        (Nat.land (Nat.land R 4294967295) 1) (a := A) (by omega)
      obtain ⟨e, l1, l2⟩ := labGo_eq di ft n k (Nat.shiftRight R 32)
        (addZ (CD (Nat.shiftRight (Nat.land R 4294967295) 1))
          (Nat.land (Nat.land R 4294967295) 1) A)
        (by omega) (by omega)
      exact ⟨e, by omega, by omega⟩
    · dsimp only
      rw [strictN_eq, strictN_eq]
      have hf : pushFwd (pwN (pcode di)) (pwN A) = pushLab (pwN (pcode di)) 0 (pwN A) := rfl
      rw [hf, pushLab_code _ _ (by omega) (by omega)]
      have hb := addZ_bd di 0 (a := A) (by omega)
      obtain ⟨e, l1, l2⟩ := labGo_eq di ft n k R (addZ di 0 A) (by omega) (by omega)
      exact ⟨e, by omega, by omega⟩

theorem labWalk_eq (i J w h : Nat) : labWalk LB i J w h = labWalkZ CD i J w h := by
  have hw : wLen w ≤ 1023 := Nat.and_le_right
  rw [labWalk_def, labWalkZ_def, hLB i, zero_eq_pwN]
  obtain ⟨e, l1, l2⟩ := labGo_eq hLB (CD i) (Nat.land (Nat.shiftRight J 37) 65535) (wLen w)
    (wLen w) (Nat.shiftRight J 53) 4294967296 (by omega) (by omega)
  rw [e]
  generalize labGoZ CD (CD i) (Nat.land (Nat.shiftRight J 37) 65535) (wLen w) (wLen w)
    (Nat.shiftRight J 53) 4294967296 = r at l1 l2
  rw [target_def, targetZ_def]
  cases Nat.beq (wKind w) 3
  · dsimp only
    rw [zero_eq_pwN]
    exact beq_pwN (by omega) (by omega) (by omega) (by omega)
  · dsimp only
    cases hh : Nat.beq h 0
    · dsimp only
      have h0 : h ≠ 0 := nbeq_ne hh
      rw [nbeq_false (show r ≠ 0 by omega)]
      obtain ⟨b, j, hb, hj, eA, _, _⟩ := pwN_shape (A := r) (by omega) (by omega)
      rw [eA]
      refine nbeq_false (mkK_ne hj 1 _ (by omega) ?_)
      by_cases hj1 : j = 1
      · right
        subst hj1
        change 0 * 256 + b ≠ 2 * h + 1
        omega
      · exact Or.inl hj1
    · dsimp only
      have h0 : h = 0 := Nat.eq_of_beq_eq_true hh
      have t : mkK 1 (2 * h + 1) = pwN 4294967297 := by
        rw [h0, pwN_hi (by omega)]
        rfl
      rw [t]
      exact beq_pwN (by omega) (by omega) (by omega) (by omega)

theorem labStep_eq : labStep LB = labStepZ CD := by
  funext Hs J S w
  rw [labStep_def, labStepZ_def, hLB, pwN_code_zero, labWalk_eq hLB]

theorem labChunk_eq (WT : Nat → Nat) : labChunk WT LB = labChunkZ WT CD := by
  funext Hs C S
  unfold labChunk labChunkZ
  rw [labStep_eq hLB]

theorem runLab_eq (WT : Nat → Nat) (Hs : Nat) : runLab WT LB Hs = runLabC WT CD Hs := by
  funext Cs S
  unfold runLab runLabC
  rw [labChunk_eq hLB]

end Run

end CFSG.KC.LabZ

end
