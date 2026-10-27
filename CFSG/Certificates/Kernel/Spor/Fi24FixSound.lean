module

public import Certificates.Data.Kernel.Spor.Fi24FixK
public import CFSG.Certificates.Kernel.Fam.Fi24Act.LibSound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

namespace CFSG.KC.Fi24FixS

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.Certificates.LceP

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> simp_all

theorem recAnd (f : ℕ → Bool) : ∀ n, Nat.rec (motive := fun _ => Bool) true
    (fun h ih => Bool.rec (motive := fun _ => Bool) false ih (f h)) n = true → ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, h, i, hi => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
    · exact recAnd f n h2 i hlt
    · exact h1

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true)
    (hm : m ≤ 64 * hi) : ∀ i < m, f i = true := by
  intro i him
  have h1 := recAnd (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi h
    (i / 64) (by omega)
  have h2 := recAnd (fun l => (fun i => bIf(Nat.blt i m, f i, true))
    (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64 h1 (i % 64) (Nat.mod_lt _ (by decide))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq, (rfl : (2 : ℕ) ^ 6 = 64)]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem sumBelow_eq (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  have rec_sum : ∀ (G : ℕ → ℕ) (k : ℕ),
      Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
        ∑ l ∈ Finset.range k, G l := by
    intro G k
    induction k with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact Nat.add_comm _ _
  have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b =
      if b = true then x else 0 := by
    intro b x
    cases b <;> rfl
  have hgen : ∀ h, sumBelow m h f =
      ∑ i ∈ Finset.range (64 * h), if i < m then f i else 0 := by
    intro h
    induction h with
    | zero =>
      rw [Nat.mul_zero, Finset.sum_range_zero]
      rfl
    | succ h ih =>
      change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
        Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + sumBelow m h f = _
      rw [rec_sum, ih, Nat.mul_succ, Finset.sum_range_add,
        Nat.add_comm (Finset.sum (Finset.range 64) _)]
      refine Nat.add_left_cancel_iff.2 (Finset.sum_congr rfl fun l _ => ?_)
      have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
        change h <<< 6 + l = 64 * h + l
        rw [Nat.shiftLeft_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
        omega
      simp only [e, sel, Nat.blt_eq]
  rw [hgen hi, show 64 * hi = m + (64 * hi - m) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := Finset.range (64 * hi - m)) (fun i _ => ite_eq_right (by omega)),
    Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => ite_eq_left (Finset.mem_range.1 hi)

theorem walk_nil (TG : ℕ → ℕ → ℕ) (r : ℕ) : walk TG [] r = r := rfl

theorem walk_cons (TG : ℕ → ℕ → ℕ) (g : ℕ) (w : List ℕ) (r : ℕ) :
    walk TG (g :: w) r = walk TG w (TG g r) := by
  change strictN (TG g r) (fun r => walk TG w r) = _
  rw [strictN_eq]

theorem walk_append (TG : ℕ → ℕ → ℕ) (u v : List ℕ) (r : ℕ) :
    walk TG (u ++ v) r = walk TG v (walk TG u r) := by
  induction u generalizing r with
  | nil => rfl
  | cons g u ih => rw [List.cons_append, walk_cons, walk_cons, ih]

theorem walk_rel {G : Type*} [Group G] (H : Subgroup G) (R gen : ℕ → G) (TG : ℕ → ℕ → ℕ)
    {L N : ℕ} (hT : ∀ g < L, ∀ i < N, TG g i < N ∧ R i * gen g * (R (TG g i))⁻¹ ∈ H) :
    ∀ w : List ℕ, (∀ g ∈ w, g < L) → ∀ i < N,
      walk TG w i < N ∧ R i * (w.map gen).prod * (R (walk TG w i))⁻¹ ∈ H := by
  intro w
  induction w with
  | nil =>
    intro _ i hi
    refine ⟨hi, ?_⟩
    rw [walk_nil, List.map_nil, List.prod_nil, mul_one, mul_inv_cancel]
    exact H.one_mem
  | cons g w ih =>
    intro hw i hi
    obtain ⟨h1, h2⟩ := hT g (hw g List.mem_cons_self) i hi
    obtain ⟨h3, h4⟩ := ih (fun x hx => hw x (List.mem_cons_of_mem g hx)) (TG g i) h1
    rw [walk_cons]
    refine ⟨h3, ?_⟩
    have e : R i * ((g :: w).map gen).prod * (R (walk TG w (TG g i)))⁻¹ =
        (R i * gen g * (R (TG g i))⁻¹) *
          (R (TG g i) * (w.map gen).prod * (R (walk TG w (TG g i)))⁻¹) := by
      rw [List.map_cons, List.prod_cons]
      group
    rw [e]
    exact H.mul_mem h2 h4

@[expose] def hgen (g : ℕ) : ℕ := if g = 8 then 10 else g + 1

theorem cl1_spec {S IX : ℕ → ℕ} {n i g y : ℕ} (h : cl1 S IX n i g y = true) :
    IX (9 * i + g) < n ∧ S (IX (9 * i + g)) = y := by
  unfold cl1 at h
  rw [letB_eq, andB_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem closOK_spec {S IX : ℕ → ℕ} {TG : ℕ → ℕ → ℕ} {n lo m hi : ℕ}
    (h : closOK S IX TG n lo m hi = true) (hm : m ≤ 64 * hi) :
    ∀ t < m, ∀ g < 9, IX (9 * (lo + t) + g) < n ∧
      S (IX (9 * (lo + t) + g)) = TG (hgen g) (TG 0 (S (lo + t))) := by
  intro t ht g hg
  have h1 := allBelow_spec h hm t ht
  simp only [letB_eq] at h1
  unfold cl9 at h1
  simp only [andB_iff] at h1
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := h1
  have e : Nat.add lo t = lo + t := rfl
  rw [e] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  interval_cases g
  · exact cl1_spec c0
  · exact cl1_spec c1
  · exact cl1_spec c2
  · exact cl1_spec c3
  · exact cl1_spec c4
  · exact cl1_spec c5
  · exact cl1_spec c6
  · exact cl1_spec c7
  · exact cl1_spec c8

theorem cntFix_eq (S : ℕ → ℕ) (TG : ℕ → ℕ → ℕ) (w u : List ℕ) (lo m hi : ℕ) (hm : m ≤ 64 * hi) :
    cntFix S TG w u lo m hi = ((Finset.range m).filter fun t =>
      walk TG u (walk TG w (S (lo + t))) = walk TG w (S (lo + t))).card := by
  unfold cntFix
  rw [sumBelow_eq _ _ _ hm, Finset.card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [strictN_eq, strictN_eq, brec_eq]
  have e : Nat.add lo t = lo + t := rfl
  rw [e]
  by_cases hc : walk TG u (walk TG w (S (lo + t))) = walk TG w (S (lo + t))
  · rw [if_pos hc, if_pos (by rw [Nat.beq_eq]; exact hc)]
  · rw [if_neg hc, if_neg (by rw [Nat.beq_eq]; exact hc)]

theorem aliveEnum_spec {LVs A : ℕ → ℕ} {nC N lo m : ℕ}
    (h : CFSG.KC.Fi24Act.aliveEnum LVs A nC N lo m = true) : lo + m ≤ N ∧ ∀ t < m,
      A (lo + t) < nC ∧ alive LVs (A (lo + t)) = true ∧
        (lo + t + 1 < N → A (lo + t) < A (lo + t + 1)) := by
  unfold CFSG.KC.Fi24Act.aliveEnum at h
  rw [andB_iff, Nat.ble_eq] at h
  refine ⟨h.1, fun t ht => ?_⟩
  have := CFSG.Certificates.Fi24ActS.rec_all (fun i => letB (A i) (fun a => andB (Nat.blt a nC)
      (andB (alive LVs a) (bIf(Nat.blt (Nat.succ i) N, Nat.blt a (A (Nat.succ i)), true)))))
    lo m h.2 t ht
  simp only [letB_eq, andB_iff, Nat.blt_eq] at this
  obtain ⟨h1, h2, h3⟩ := this
  refine ⟨h1, h2, fun hlt => ?_⟩
  rw [brec_eq, if_pos (by rw [Nat.blt_eq]; exact hlt), Nat.blt_eq] at h3
  exact h3

theorem bitAt_eq (z o : ℕ) : bitAt z o = (z.testBit o).toNat := by
  unfold bitAt
  change (z >>> o) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.toNat_testBit, Nat.shiftRight_eq_div_pow]

theorem RM_eq : RM = 2 ^ 781 - 1 := by
  change 1 <<< 781 - 1 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_row (P o i : ℕ) (hi : i < 781) :
    (Nat.land (Nat.shiftRight P o) RM).testBit i = P.testBit (o + i) := by
  change ((P >>> o) &&& RM).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, RM_eq, Nat.testBit_two_pow_sub_one]
  simp [hi]

theorem entOK_spec {z1 z2 o v : ℕ} (h : entOK z1 z2 o v = true) :
    z1.testBit o = decide (v = 1) ∧ z2.testBit o = decide (v = 2) := by
  unfold entOK at h
  rw [andB_iff, Nat.beq_eq, Nat.beq_eq, bitAt_eq, bitAt_eq, brec_eq, brec_eq] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · by_cases hv : v = 1
    · rw [if_pos (by rw [Nat.beq_eq]; exact hv)] at h1
      cases hb : z1.testBit o <;> simp_all
    · rw [if_neg (by rw [Nat.beq_eq]; exact hv)] at h1
      cases hb : z1.testBit o <;> simp_all
  · by_cases hv : v = 2
    · rw [if_pos (by rw [Nat.beq_eq]; exact hv)] at h2
      cases hb : z2.testBit o <;> simp_all
    · rw [if_neg (by rw [Nat.beq_eq]; exact hv)] at h2
      cases hb : z2.testBit o <;> simp_all

theorem trit_eq (x s : ℕ) (hs : s < 4) : trit x s = x / 3 ^ s % 3 := by
  unfold trit
  rw [brec_eq, brec_eq, brec_eq]
  interval_cases s <;> rfl

theorem digitsOK_spec {CT : ℕ → ℕ} {len : ℕ} : ∀ (cs : List Char) (t : ℕ),
    digitsOK CT len cs t = true →
      t + cs.length = len ∧ ∀ k < cs.length, CT (t + k) = d81 cs[k]!.toNat
  | [], t, h => by
    refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    change Nat.beq t len = true at h
    rw [Nat.beq_eq] at h
    simpa using h
  | ch :: cs, t, h => by
    change andB (Nat.beq (CT t) (d81 ch.toNat)) (letB (Nat.succ t) (fun t => digitsOK CT len cs t))
      = true at h
    rw [andB_iff, letB_eq, Nat.beq_eq] at h
    obtain ⟨h1, h2⟩ := digitsOK_spec cs (t + 1) h.2
    refine ⟨by rw [List.length_cons]; omega, fun k hk => ?_⟩
    rcases k with _ | k
    · simpa using h.1
    · have := h2 k (by rw [List.length_cons] at hk; omega)
      rw [show t + (k + 1) = t + 1 + k by omega]
      simpa using this

theorem colsOK_spec {P1 P2 : ℕ} {CT : ℕ → ℕ} (h : colsOK P1 P2 CT = true) : ∀ j < 528, ∀ i < 253,
    P1.testBit (781 * (253 + j) + i) = decide (CT (132 * i + j / 4) / 3 ^ (j % 4) % 3 = 1) ∧
      P2.testBit (781 * (253 + j) + i) = decide (CT (132 * i + j / 4) / 3 ^ (j % 4) % 3 = 2) := by
  intro j hj i hi
  have h1 := allBelow_spec h (by norm_num) j hj
  simp only [letB_eq] at h1
  have h2 := allBelow_spec h1 (by norm_num) i hi
  obtain ⟨a, b⟩ := entOK_spec h2
  rw [testBit_row _ _ _ (by omega)] at a b
  have e : Nat.mul 781 (Nat.add 253 j) = 781 * (253 + j) := rfl
  have e2 : Nat.add (Nat.mul 132 i) (Nat.div j 4) = 132 * i + j / 4 := rfl
  have e3 : Nat.mod j 4 = j % 4 := rfl
  rw [e, e2, e3, trit_eq _ _ (Nat.mod_lt _ (by norm_num))] at a b
  exact ⟨a, b⟩

theorem rowsZOK_spec {P1 P2 : ℕ} (h : rowsZOK P1 P2 = true) : ∀ j < 781, ∀ i < 781,
    (j < 253 → P1.testBit (781 * j + i) = decide (i = j) ∧ P2.testBit (781 * j + i) = false) ∧
      (253 ≤ j → 253 ≤ i → P1.testBit (781 * j + i) = false ∧ P2.testBit (781 * j + i) = false) := by
  intro j hj i hi
  have h1 := allBelow_spec h (by norm_num) j hj
  simp only [letB_eq] at h1
  have hrow : ∀ P : ℕ, (Nat.land (Nat.shiftRight P (Nat.mul 781 j)) RM).testBit i =
      P.testBit (781 * j + i) := by
    intro P
    change ((P >>> (781 * j)) &&& RM).testBit i = _
    rw [Nat.testBit_and, Nat.testBit_shiftRight, RM_eq, Nat.testBit_two_pow_sub_one]
    simp [hi]
  rw [brec_eq] at h1
  constructor
  · intro hj2
    rw [if_pos (by rw [Nat.blt_eq]; exact hj2), andB_iff, Nat.beq_eq, Nat.beq_eq] at h1
    obtain ⟨a, b⟩ := h1
    rw [← hrow, ← hrow, a, b]
    refine ⟨?_, Nat.zero_testBit i⟩
    change (1 <<< j).testBit i = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases e : i = j
    · simp [e]
    · simp [e, Ne.symm e]
  · intro hj2 hi2
    rw [if_neg (by rw [Nat.blt_eq]; omega), andB_iff, Nat.beq_eq, Nat.beq_eq] at h1
    obtain ⟨a, b⟩ := h1
    rw [← hrow, ← hrow]
    have ea := congrArg (fun x => x.testBit (i - 253)) a
    have eb := congrArg (fun x => x.testBit (i - 253)) b
    simp only [Nat.zero_testBit] at ea eb
    change (_ >>> 253).testBit (i - 253) = false at ea
    change (_ >>> 253).testBit (i - 253) = false at eb
    rw [Nat.testBit_shiftRight, show 253 + (i - 253) = i by omega] at ea eb
    exact ⟨ea, eb⟩

end CFSG.KC.Fi24FixS

end
