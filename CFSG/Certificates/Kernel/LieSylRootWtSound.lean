module

public import Certificates.Data.Kernel.LieSylRootWtK
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace Certificates.Data.LieSylRootWtK

open Certificates.Data.LieSylRootWt CFSG.KC.Loop

theorem allK_cons (f : Nat → Bool) (x : Nat) (l : List Nat) :
    allK f (x :: l) = (f x && allK f l) := rfl

theorem allK_eq (f : Nat → Bool) : ∀ l : List Nat, allK f l = l.all f
  | [] => rfl
  | x :: l => by rw [allK_cons, allK_eq f l, List.all_cons]

theorem getK_eq : ∀ (l : List Nat) (i : Nat), getK l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getK_eq l i

theorem getLK_eq : ∀ (l : List (List Nat)) (i : Nat), getLK l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getLK_eq l i

theorem appK_eq (x : Nat) : ∀ l : List Nat, appK l x = l ++ [x]
  | [] => rfl
  | y :: l => congrArg (y :: ·) (appK_eq x l)

theorem strictBK_eq (y : Nat) (k : Nat → Bool) : strictBK y k = k y := by
  cases y <;> rfl

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem getD_map' {α β : Type} (f : α → β) (d : α) :
    ∀ (l : List α) (n : Nat), (l.map f).getD n (f d) = f (l.getD n d)
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, n + 1 => getD_map' f d l n

theorem all_congr' {α : Type} {f g : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.all f = l.all g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      all_congr' fun y hy => h y (List.mem_cons_of_mem x hy)]

theorem rI_lt (v : List Int) (i : Nat) : rI v i < 11 := by
  unfold rI
  have h1 := Int.emod_nonneg (v.getD i 0) (by decide : (11 : Int) ≠ 0)
  have h2 := Int.emod_lt_of_pos (v.getD i 0) (by decide : (0 : Int) < 11)
  omega

theorem rI_cast (v : List Int) (i : Nat) : (rI v i : Int) = v.getD i 0 % 11 := by
  unfold rI
  have h1 := Int.emod_nonneg (v.getD i 0) (by decide : (11 : Int) ≠ 0)
  omega

theorem l0_eq (x : Nat) : l0 x = x % 65536 := rfl
theorem l1_eq (x : Nat) : l1 x = x / 65536 % 65536 := rfl
theorem l2_eq (x : Nat) : l2 x = x / 4294967296 % 65536 := rfl
theorem l3_eq (x : Nat) : l3 x = x / 281474976710656 % 65536 := rfl

theorem lanes {a b c d : Nat} (ha : a < 65536) (hb : b < 65536) (hc : c < 65536) (hd : d < 65536) :
    l0 (a + 65536 * b + 4294967296 * c + 281474976710656 * d) = a ∧
      l1 (a + 65536 * b + 4294967296 * c + 281474976710656 * d) = b ∧
      l2 (a + 65536 * b + 4294967296 * c + 281474976710656 * d) = c ∧
      l3 (a + 65536 * b + 4294967296 * c + 281474976710656 * d) = d := by
  rw [l0_eq, l1_eq, l2_eq, l3_eq]
  omega

theorem pvI_nil : pvI [] = 0 := rfl

theorem wK_eq (bp : Nat) (cs : List Nat) :
    wK bp cs = (l0 bp * getK cs 0 + l1 bp * getK cs 1) + (l2 bp * getK cs 2 + l3 bp * getK cs 3) :=
  rfl

theorem redP_eq (w : Nat) :
    redP w = (l0 w % 11 + 65536 * (l1 w % 11)) +
      (4294967296 * (l2 w % 11) + 281474976710656 * (l3 w % 11)) := rfl

theorem keyK_eq (w : Nat) :
    keyK w = (l0 w % 11 + 16 * (l1 w % 11)) + (256 * (l2 w % 11) + 4096 * (l3 w % 11)) := rfl

theorem getK_map (γs : List (List Int)) (j : Nat) : getK (γs.map pvI) j = pvI (γs.getD j []) := by
  rw [getK_eq, ← pvI_nil, getD_map']

@[expose] def sI (b : List Int) (γs : List (List Int)) (i : Nat) : Nat :=
  rI b 0 * rI (γs.getD 0 []) i + rI b 1 * rI (γs.getD 1 []) i + rI b 2 * rI (γs.getD 2 []) i +
    rI b 3 * rI (γs.getD 3 []) i

theorem sI_lt (b : List Int) (γs : List (List Int)) (i : Nat) : sI b γs i < 401 := by
  have h : ∀ j, rI b j * rI (γs.getD j []) i ≤ 10 * 10 := fun j =>
    Nat.mul_le_mul (Nat.le_of_lt_succ (rI_lt b j)) (Nat.le_of_lt_succ (rI_lt _ i))
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  unfold sI
  generalize rI b 0 * rI (γs.getD 0 []) i = p0 at h0 ⊢
  generalize rI b 1 * rI (γs.getD 1 []) i = p1 at h1 ⊢
  generalize rI b 2 * rI (γs.getD 2 []) i = p2 at h2 ⊢
  generalize rI b 3 * rI (γs.getD 3 []) i = p3 at h3 ⊢
  omega

theorem wK_pk (b : List Int) (γs : List (List Int)) :
    wK (pvI b) (γs.map pvI) =
      sI b γs 0 + 65536 * sI b γs 1 + 4294967296 * sI b γs 2 + 281474976710656 * sI b γs 3 := by
  obtain ⟨e0, e1, e2, e3⟩ := lanes (Nat.lt_trans (rI_lt b 0) (by decide))
    (Nat.lt_trans (rI_lt b 1) (by decide)) (Nat.lt_trans (rI_lt b 2) (by decide))
    (Nat.lt_trans (rI_lt b 3) (by decide))
  rw [wK_eq, getK_map, getK_map, getK_map, getK_map]
  unfold pvI
  rw [e0, e1, e2, e3]
  unfold sI
  ring

theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl

theorem combo_getD (b : List Int) (γs : List (List Int)) {i : Nat} (hi : i < 4) :
    (combo 4 b γs).getD i 0 =
      b.getD 0 0 * (γs.getD 0 []).getD i 0 + b.getD 1 0 * (γs.getD 1 []).getD i 0 +
        b.getD 2 0 * (γs.getD 2 []).getD i 0 + b.getD 3 0 * (γs.getD 3 []).getD i 0 := by
  have e : (combo 4 b γs).getD i 0 = comboAt 4 b γs i := by
    unfold combo
    rw [range4]
    interval_cases i <;> rfl
  rw [e]
  unfold comboAt
  rw [range4]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

theorem rI_combo (b : List Int) (γs : List (List Int)) {i : Nat} (hi : i < 4) :
    rI (combo 4 b γs) i = sI b γs i % 11 := by
  have hc : (sI b γs i : Int) =
      (b.getD 0 0 % 11) * ((γs.getD 0 []).getD i 0 % 11) +
        (b.getD 1 0 % 11) * ((γs.getD 1 []).getD i 0 % 11) +
        (b.getD 2 0 % 11) * ((γs.getD 2 []).getD i 0 % 11) +
        (b.getD 3 0 % 11) * ((γs.getD 3 []).getD i 0 % 11) := by
    unfold sI
    push_cast
    rw [rI_cast, rI_cast, rI_cast, rI_cast, rI_cast, rI_cast, rI_cast, rI_cast]
  have m0 := Int.mul_emod (b.getD 0 0) ((γs.getD 0 []).getD i 0) 11
  have m1 := Int.mul_emod (b.getD 1 0) ((γs.getD 1 []).getD i 0) 11
  have m2 := Int.mul_emod (b.getD 2 0) ((γs.getD 2 []).getD i 0) 11
  have m3 := Int.mul_emod (b.getD 3 0) ((γs.getD 3 []).getD i 0) 11
  unfold rI
  rw [combo_getD b γs hi]
  generalize b.getD 0 0 * (γs.getD 0 []).getD i 0 = P0 at m0 ⊢
  generalize b.getD 1 0 * (γs.getD 1 []).getD i 0 = P1 at m1 ⊢
  generalize b.getD 2 0 * (γs.getD 2 []).getD i 0 = P2 at m2 ⊢
  generalize b.getD 3 0 * (γs.getD 3 []).getD i 0 = P3 at m3 ⊢
  generalize b.getD 0 0 % 11 * ((γs.getD 0 []).getD i 0 % 11) = Q0 at m0 hc
  generalize b.getD 1 0 % 11 * ((γs.getD 1 []).getD i 0 % 11) = Q1 at m1 hc
  generalize b.getD 2 0 % 11 * ((γs.getD 2 []).getD i 0 % 11) = Q2 at m2 hc
  generalize b.getD 3 0 % 11 * ((γs.getD 3 []).getD i 0 % 11) = Q3 at m3 hc
  omega

theorem redP_wK (b : List Int) (γs : List (List Int)) :
    redP (wK (pvI b) (γs.map pvI)) = pvI (combo 4 b γs) := by
  obtain ⟨e0, e1, e2, e3⟩ := lanes (Nat.lt_trans (sI_lt b γs 0) (by decide))
    (Nat.lt_trans (sI_lt b γs 1) (by decide)) (Nat.lt_trans (sI_lt b γs 2) (by decide))
    (Nat.lt_trans (sI_lt b γs 3) (by decide))
  rw [wK_pk, redP_eq, e0, e1, e2, e3]
  unfold pvI
  rw [rI_combo b γs (by decide : 0 < 4), rI_combo b γs (by decide : 1 < 4),
    rI_combo b γs (by decide : 2 < 4), rI_combo b γs (by decide : 3 < 4)]
  omega

theorem keyK_wK (b : List Int) (γs : List (List Int)) :
    keyK (wK (pvI b) (γs.map pvI)) = kvI (combo 4 b γs) := by
  obtain ⟨e0, e1, e2, e3⟩ := lanes (Nat.lt_trans (sI_lt b γs 0) (by decide))
    (Nat.lt_trans (sI_lt b γs 1) (by decide)) (Nat.lt_trans (sI_lt b γs 2) (by decide))
    (Nat.lt_trans (sI_lt b γs 3) (by decide))
  rw [wK_pk, keyK_eq, e0, e1, e2, e3]
  unfold kvI
  rw [rI_combo b γs (by decide : 0 < 4), rI_combo b γs (by decide : 1 < 4),
    rI_combo b γs (by decide : 2 < 4), rI_combo b γs (by decide : 3 < 4)]
  omega

theorem red_zero : red 11 0 = 0 := rfl

theorem redV_getD (v : List Int) (i : Nat) : (redV 11 v).getD i 0 = red 11 (v.getD i 0) := by
  have h := getD_map' (red 11) 0 v i
  rw [red_zero] at h
  exact h

theorem rI_redV (v : List Int) (i : Nat) : rI (redV 11 v) i = rI v i := by
  unfold rI
  rw [redV_getD]
  unfold red
  have h1 := Int.emod_nonneg (v.getD i 0) (by decide : (11 : Int) ≠ 0)
  omega

theorem pvI_redV (v : List Int) : pvI (redV 11 v) = pvI v := by
  unfold pvI
  rw [rI_redV, rI_redV, rI_redV, rI_redV]

theorem kvI_redV (v : List Int) : kvI (redV 11 v) = kvI v := by
  unfold kvI
  rw [rI_redV, rI_redV, rI_redV, rI_redV]

theorem len4 {x : List Int} (h : x.length = 4) : ∃ a b c d, x = [a, b, c, d] := by
  match x, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem redV4 (a b c d : Int) : redV 11 [a, b, c, d] = [a % 11, b % 11, c % 11, d % 11] := rfl

theorem rI4 (a b c d : Int) : rI [a, b, c, d] 0 = (a % 11).toNat ∧ rI [a, b, c, d] 1 = (b % 11).toNat ∧
    rI [a, b, c, d] 2 = (c % 11).toNat ∧ rI [a, b, c, d] 3 = (d % 11).toNat := ⟨rfl, rfl, rfl, rfl⟩

theorem redV_eq_of_rI {x y : List Int} (hx : x.length = 4) (hy : y.length = 4)
    (h : ∀ i < 4, rI x i = rI y i) : redV 11 x = redV 11 y := by
  obtain ⟨a, b, c, d, rfl⟩ := len4 hx
  obtain ⟨a', b', c', d', rfl⟩ := len4 hy
  obtain ⟨r0, r1, r2, r3⟩ := rI4 a b c d
  obtain ⟨s0, s1, s2, s3⟩ := rI4 a' b' c' d'
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [r0, s0] at h0
  rw [r1, s1] at h1
  rw [r2, s2] at h2
  rw [r3, s3] at h3
  rw [redV4, redV4]
  have p0 := Int.emod_nonneg a (by decide : (11 : Int) ≠ 0)
  have p1 := Int.emod_nonneg b (by decide : (11 : Int) ≠ 0)
  have p2 := Int.emod_nonneg c (by decide : (11 : Int) ≠ 0)
  have p3 := Int.emod_nonneg d (by decide : (11 : Int) ≠ 0)
  have q0 := Int.emod_nonneg a' (by decide : (11 : Int) ≠ 0)
  have q1 := Int.emod_nonneg b' (by decide : (11 : Int) ≠ 0)
  have q2 := Int.emod_nonneg c' (by decide : (11 : Int) ≠ 0)
  have q3 := Int.emod_nonneg d' (by decide : (11 : Int) ≠ 0)
  have e0 : a % 11 = a' % 11 := by omega
  have e1 : b % 11 = b' % 11 := by omega
  have e2 : c % 11 = c' % 11 := by omega
  have e3 : d % 11 = d' % 11 := by omega
  rw [e0, e1, e2, e3]

theorem redV_eq_of_kvI {x y : List Int} (hx : x.length = 4) (hy : y.length = 4)
    (h : kvI x = kvI y) : redV 11 x = redV 11 y := by
  refine redV_eq_of_rI hx hy fun i hi => ?_
  have := rI_lt x 0
  have := rI_lt x 1
  have := rI_lt x 2
  have := rI_lt x 3
  have := rI_lt y 0
  have := rI_lt y 1
  have := rI_lt y 2
  have := rI_lt y 3
  unfold kvI at h
  interval_cases i <;> omega

theorem redV_eq_of_pvI {x y : List Int} (hx : x.length = 4) (hy : y.length = 4)
    (h : pvI x = pvI y) : redV 11 x = redV 11 y := by
  refine redV_eq_of_rI hx hy fun i hi => ?_
  have := rI_lt x 0
  have := rI_lt x 1
  have := rI_lt x 2
  have := rI_lt x 3
  have := rI_lt y 0
  have := rI_lt y 1
  have := rI_lt y 2
  have := rI_lt y 3
  unfold pvI at h
  interval_cases i <;> omega

theorem length_combo (b : List Int) (γs : List (List Int)) : (combo 4 b γs).length = 4 := by
  simp [combo]

theorem length_redV (v : List Int) : (redV 11 v).length = v.length := by
  simp [redV]

theorem redV_redV (v : List Int) : redV 11 (redV 11 v) = redV 11 v := by
  unfold redV
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  unfold red
  simp

theorem testBit_maskOf (n : Nat) : ∀ L : List Nat, (maskOf L).testBit n = true ↔ n ∈ L
  | [] => by simp [maskOf]
  | k :: L => by
    have e : maskOf (k :: L) = maskOf L ||| (1 <<< k) := rfl
    rw [e, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
      testBit_maskOf n L, List.mem_cons, decide_eq_true_iff]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm), fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

theorem beq_bit (m n : Nat) :
    Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1 = m.testBit n := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight m n) 1 = m / 2 ^ n % 2 := by
    change (m >>> n) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e]
  apply Bool.eq_iff_iff.mpr
  rw [Nat.beq_eq, decide_eq_true_iff]

theorem contains_eq (R : List (List Int)) (hR : ∀ ρ ∈ R, ρ.length = 4) (x : List Int)
    (hx : x.length = 4) (mask : Nat) (hm : mask = maskOf (R.map kvI)) :
    (R.map (redV 11)).contains (redV 11 x) = mask.testBit (kvI x) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, hm, testBit_maskOf, List.mem_map, List.mem_map]
  constructor
  · rintro ⟨ρ, hρ, e⟩
    refine ⟨ρ, hρ, ?_⟩
    rw [← kvI_redV ρ, e, kvI_redV]
  · rintro ⟨ρ, hρ, e⟩
    exact ⟨ρ, hρ, redV_eq_of_kvI (hR ρ hρ) hx e⟩

theorem testK_eq (R : List (List Int)) (hR : ∀ ρ ∈ R, ρ.length = 4) (mask : Nat)
    (hm : mask = maskOf (R.map kvI)) (b : List Int) (γs : List (List Int)) :
    testK mask (pvI b) (γs.map pvI) = (R.map (redV 11)).contains (redV 11 (combo 4 b γs)) := by
  unfold testK
  rw [strictBK_eq, beq_bit, keyK_wK, contains_eq R hR _ (length_combo b γs) mask hm]

theorem iterN_eq {α : Type} (f : α → α) : ∀ (n : Nat) (x : α), iterN f n x = f^[n] x
  | 0, _ => rfl
  | n + 1, x => by
    rw [Function.iterate_succ_apply, ← iterN_eq f n (f x)]
    rfl

theorem itK_eq (cs : List Nat) : ∀ (n x : Nat), itK cs n x = (stepK cs)^[n] x
  | 0, _ => rfl
  | n + 1, x => by
    rw [Function.iterate_succ_apply', ← itK_eq cs n x]
    exact strictN_eq' _ _

theorem stepK_pk (γs : List (List Int)) (v : List Int) :
    stepK (γs.map pvI) (pvI v) = pvI (redV 11 (combo 4 v γs)) := by
  unfold stepK
  rw [strictN_eq', redP_wK, pvI_redV]

theorem pvI_iter (γs : List (List Int)) (n : Nat) (v : List Int) :
    pvI ((fun v => redV 11 (combo 4 v γs))^[n] v) = (stepK (γs.map pvI))^[n] (pvI v) :=
  Function.Semiconj.iterate_right (f := pvI) (fun v => (stepK_pk γs v).symm) n v

theorem iter_reduced (γs : List (List Int)) (n : Nat) {v : List Int} (hl : v.length = 4)
    (hr : redV 11 v = v) :
    ((fun v => redV 11 (combo 4 v γs))^[n] v).length = 4 ∧
      redV 11 ((fun v => redV 11 (combo 4 v γs))^[n] v) =
        (fun v => redV 11 (combo 4 v γs))^[n] v := by
  induction n with
  | zero => exact ⟨hl, hr⟩
  | succ n _ =>
    rw [Function.iterate_succ_apply']
    exact ⟨by rw [length_redV, length_combo], redV_redV _⟩

theorem unit_reduced (j : Nat) : (unitVec 4 j).length = 4 ∧ redV 11 (unitVec 4 j) = unitVec 4 j := by
  refine ⟨by simp [unitVec], ?_⟩
  unfold redV unitVec
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply]
  unfold red
  split_ifs <;> decide

theorem leaf_eq (γs : List (List Int)) (e j : Nat) :
    (iterN (fun v => redV 11 (combo 4 v γs)) e (unitVec 4 j) == redV 11 (unitVec 4 j)) =
      Nat.beq (itK (γs.map pvI) e (pvI (unitVec 4 j))) (pvI (unitVec 4 j)) := by
  obtain ⟨hl, hr⟩ := unit_reduced j
  obtain ⟨hl', hr'⟩ := iter_reduced γs e hl hr
  rw [iterN_eq, itK_eq, ← pvI_iter, hr]
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    rw [h]
  · intro h
    exact hr'.symm.trans ((redV_eq_of_pvI hl' hl h).trans hr)

theorem orderK_eq (e : Nat) (cs : List Nat) :
    orderK e cs = (Nat.beq (itK cs e 1) 1 && (Nat.beq (itK cs e 65536) 65536 &&
      (Nat.beq (itK cs e 4294967296) 4294967296 &&
        Nat.beq (itK cs e 281474976710656) 281474976710656))) := rfl

theorem orderOK_eq (γs : List (List Int)) (e : Nat) :
    orderOK 11 e 4 γs = orderK e (γs.map pvI) := by
  unfold orderOK
  rw [range4, orderK_eq]
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [leaf_eq, leaf_eq, leaf_eq, leaf_eq]
  rfl

theorem searchK_zero (RP : List Nat) (LP : List (List Nat)) (mask e k : Nat) (cs : List Nat) :
    searchK RP LP mask e 0 k cs = orderK e cs := rfl

theorem searchK_succ (RP : List Nat) (LP : List (List Nat)) (mask e fuel k : Nat) (cs : List Nat) :
    searchK RP LP mask e (fuel + 1) k cs =
      Bool.rec (motive := fun _ => Bool) (orderK e cs)
        (allK (fun g => (!allK (fun bp => testK mask bp (appK cs g)) (getLK LP k)) ||
          searchK RP LP mask e fuel (k + 1) (appK cs g)) RP) (Nat.blt k 4) := rfl

theorem search_eq (R : List (List Int)) (hR : ∀ ρ ∈ R, ρ.length = 4) (mask : Nat)
    (hm : mask = maskOf (R.map kvI)) (e : Nat) :
    ∀ (fuel k : Nat) (p : List (List Int)),
      searchOK 11 e 4 R (R.map (redV 11)) (levels4 R) fuel k p =
        searchK (R.map pvI) ((levels4 R).map (List.map pvI)) mask e fuel k (p.map pvI)
  | 0, k, p => by
    rw [searchK_zero, ← orderOK_eq]
    rfl
  | fuel + 1, k, p => by
    rw [searchK_succ]
    by_cases hk : k < 4
    · have hb : Nat.blt k 4 = true := Nat.blt_eq.mpr hk
      rw [hb]
      simp only [searchOK, if_pos hk]
      rw [allK_eq, List.all_map]
      apply all_congr'
      intro γ _
      have ha : appK (p.map pvI) (pvI γ) = (p ++ [γ]).map pvI := by
        rw [appK_eq, List.map_append, List.map_cons, List.map_nil]
      have hL : getLK ((levels4 R).map (List.map pvI)) k = ((levels4 R).getD k []).map pvI := by
        rw [getLK_eq]
        exact getD_map' (List.map pvI) [] (levels4 R) k
      simp only [Function.comp_apply]
      rw [ha, hL, allK_eq, List.all_map, ← search_eq R hR mask hm e fuel (k + 1) (p ++ [γ])]
      congr 2
      apply all_congr'
      intro b _
      simp only [Function.comp_apply]
      rw [testK_eq R hR mask hm]
    · have hb : Nat.blt k 4 = false := by
        cases h : Nat.blt k 4
        · rfl
        · exact absurd (Nat.blt_eq.mp h) hk
      rw [hb]
      simp only [searchOK, if_neg hk]
      exact orderOK_eq p e

theorem stabCheck_eq (R : List (List Int)) (hR : ∀ ρ ∈ R, ρ.length = 4) (mask : Nat)
    (hm : mask = maskOf (R.map kvI)) (e : Nat) :
    stabCheck 11 e 4 R = searchK (R.map pvI) ((levels4 R).map (List.map pvI)) mask e 4 0 [] :=
  search_eq R hR mask hm e 4 0 []

theorem length_roots (t : Ty) : ∀ ρ ∈ t.roots, ρ.length = t.rank := by
  intro ρ hρ
  unfold Ty.roots at hρ
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hρ
  simp [decodeVec]

end Certificates.Data.LieSylRootWtK

end
