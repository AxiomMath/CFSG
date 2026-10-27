module

public import Certificates.Data.Kernel.D4Q2K.ElimDefs
public import Certificates.Data.Kernel.RankElim
public import Certificates.Data.CFSGNative.D4Q2.Check

public section

namespace CFSG.KC.D4Q2K

open CFSG.ClassicalInvolution.PhanDn.D4Q2 CFSG.KC.Enum

theorem allBlk_get {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (b + l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) = true
      at h
    cases h1 : f (Nat.add b len) <;> rw [h1] at h
    · exact absurd (h : false = true) Bool.false_ne_true
    rcases Nat.lt_or_ge l len with h2 | h2
    · exact allBlk_get h l h2
    · have e : l = len := by omega
      subst e
      exact h1

theorem el_strictB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem el_strictN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem el_bAnd (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem el_or (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

theorem el_ne {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  subst e
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem el_zero_add (k : Nat) : nat_lit 0 + k = k := Nat.zero_add k

theorem el_pts (P : Array Nat) (F : Array (Array Nat)) : (mkTabs P F).pts = P := rfl

theorem el_eq_of_mem : ∀ {l₁ l₂ : List Nat}, l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) →
    (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by cases (h b).2 (List.mem_cons.mpr (Or.inl rfl))
  | a :: _, [], _, _, h => by cases (h a).1 (List.mem_cons.mpr (Or.inl rfl))
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).1 (List.mem_cons.mpr (Or.inl rfl))) with e | e
      · exact e
      · rcases List.mem_cons.mp ((h b).2 (List.mem_cons.mpr (Or.inl rfl))) with e' | e'
        · exact e'.symm
        · have := h₂.1 a e
          have := h₁.1 b e'
          omega
    subst hab
    congr 1
    apply el_eq_of_mem h₁.2 h₂.2
    intro c
    constructor
    · intro hc
      rcases List.mem_cons.mp ((h c).1 (List.mem_cons_of_mem _ hc)) with e | e
      · have := h₁.1 c hc
        omega
      · exact e
    · intro hc
      rcases List.mem_cons.mp ((h c).2 (List.mem_cons_of_mem _ hc)) with e | e
      · have := h₂.1 c hc
        omega
      · exact e

theorem el_map_succ (f : Nat → Nat) (n k : Nat) :
    (List.range (n + 1)).map (fun i => f (k + i)) =
      f k :: (List.range n).map (fun i => f (Nat.succ k + i)) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply]
  congr 1
  omega

theorem el_walk (l E : Nat) : ∀ (n k b acc : Nat), walkR l E n k b acc = true →
    (∀ y ∈ (List.range n).map (fun i => nbAt l (k + i)), b ≤ y ∧ y < 6720) ∧
    ((List.range n).map (fun i => nbAt l (k + i))).Pairwise (· < ·) ∧
    acc + (((List.range n).map (fun i => nbAt l (k + i))).map fun y => 2 ^ (64 + y) + 1).sum = E
  | 0, k, b, acc, h => by
    have e : acc = E := Nat.eq_of_beq_eq_true h
    subst e
    simp
  | n + 1, k, b, acc, h => by
    change strictB (nbAt l k) (fun y => Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool) false
        (strictB (Nat.succ (Nat.add acc (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) y))))
          fun acc' => walkR l E n (Nat.succ k) (Nat.succ y) acc') (Nat.blt y (nat_lit 6720)))
      (Nat.ble b y)) = true at h
    simp only [el_strictB, el_bAnd, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ih1, ih2, ih3⟩ := el_walk l E n _ _ _ h3
    rw [el_map_succ]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_cons.mp hz with e | e
      · subst e
        exact ⟨h1, h2⟩
      · have := ih1 z e
        omega
    · rw [List.pairwise_cons]
      exact ⟨fun z hz => (ih1 z hz).1, ih2⟩
    · rw [List.map_cons, List.sum_cons]
      have e : Nat.shiftLeft 1 (64 + nbAt l k) = 2 ^ (64 + nbAt l k) := Nat.one_shiftLeft _
      have ih4 : acc + Nat.shiftLeft 1 (64 + nbAt l k) + 1 +
          (((List.range n).map (fun i => nbAt l (Nat.succ k + i))).map
            fun y => 2 ^ (64 + y) + 1).sum = E := ih3
      rw [e] at ih4
      omega

theorem el_sum : ∀ ys : List Nat,
    (ys.map fun y => 2 ^ (64 + y) + 1).sum = 2 ^ 64 * (ys.map fun y => 2 ^ y).sum + ys.length
  | [] => rfl
  | y :: ys => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.length_cons, el_sum ys,
      Nat.pow_add, Nat.mul_add]
    omega

theorem el_dvd (m : Nat) : ∀ ys : List Nat, (∀ z ∈ ys, m ≤ z) →
    2 ^ m ∣ (ys.map fun y => 2 ^ y).sum
  | [], _ => Nat.dvd_zero _
  | y :: ys, h => by
    rw [List.map_cons, List.sum_cons]
    exact Nat.dvd_add (Nat.pow_dvd_pow 2 (h y (List.mem_cons.mpr (Or.inl rfl))))
      (el_dvd m ys fun z hz => h z (List.mem_cons_of_mem _ hz))

theorem el_bits : ∀ ys : List Nat, ys.Pairwise (· < ·) →
    ∀ j, Nat.testBit (ys.map fun y => 2 ^ y).sum j = decide (j ∈ ys)
  | [], _, j => by simp
  | y :: ys, h, j => by
    rw [List.pairwise_cons] at h
    obtain ⟨Q, hQ⟩ := el_dvd (y + 1) ys fun z hz => h.1 z hz
    have ih := el_bits ys h.2 j
    rw [List.map_cons, List.sum_cons, hQ, Nat.add_comm,
      Nat.testBit_two_pow_mul_add _ (Nat.pow_lt_pow_right (by decide) (Nat.lt_add_one y)),
      Nat.testBit_two_pow]
    simp only [List.mem_cons]
    rw [hQ, ← Nat.add_zero (2 ^ (y + 1) * Q),
      Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos _), Nat.zero_testBit] at ih
    by_cases hj : j < y + 1
    · rw [if_pos hj] at ih ⊢
      have hm : j ∉ ys := fun hm => by
        have := h.1 j hm
        omega
      by_cases he : y = j
      · subst he
        simp
      · rw [decide_eq_false he, decide_eq_false]
        rintro (e | e)
        · exact he e.symm
        · exact hm e
    · rw [if_neg hj] at ih ⊢
      rw [ih]
      have he : j ≠ y := by omega
      simp [he]

theorem el_rowOf_pt {A S M TF : Nat → Nat} {x : Nat} (hx : x < 2240) :
    rowOf A S M TF x = A x ||| S x <<< 2240 := by
  have hb : Nat.blt x (nat_lit 2240) = true := Nat.blt_eq.mpr hx
  unfold rowOf
  rw [hb]
  rfl

theorem el_rowOf_sol {A S M TF : Nat → Nat} {x : Nat} (hx : ¬x < 2240) :
    rowOf A S M TF x = M (x - 2240) ||| TF (x - 2240) <<< 2240 := by
  have hb : Nat.blt x (nat_lit 2240) = false := by
    cases h : Nat.blt x (nat_lit 2240)
    · rfl
    · exact absurd (Nat.blt_eq.mp h) hx
  unfold rowOf
  rw [hb]
  exact el_strictN _ _

theorem el_tb_false {a m y : Nat} (ha : a < 2 ^ m) (hy : m ≤ y) : Nat.testBit a y = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right Nat.zero_lt_two hy))

theorem el_rowbit {A S M TF : Nat → Nat} {F : Array (Array Nat)}
    (hA : ∀ i < 2240, A i < 2 ^ 2240 ∧
      ∀ i' < 2240, Nat.testBit (A i) i' = ptAdjC (ptCodes ())[i]! (ptCodes ())[i']!)
    (hS : ∀ i < 2240, S i < 2 ^ 4480 ∧
      ∀ j < 4480, Nat.testBit (S i) j = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hM : ∀ j < 4480, M j < 2 ^ 2240 ∧
      ∀ i < 2240, Nat.testBit (M j) i = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hT : ∀ j < 4480, TF j < 2 ^ 4480 ∧
      ∀ j' < 4480, Nat.testBit (TF j) j' = (j != j' && triTest (mkTabs (ptCodes ()) F) j j'))
    {x y : Nat} (hx : x < 6720) (hy : y < 6720) :
    Nat.testBit (rowOf A S M TF x) y = adjT (mkTabs (ptCodes ()) F) x y := by
  unfold adjT
  by_cases hx1 : x < 2240
  · rw [el_rowOf_pt hx1, if_pos hx1, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hy1 : y < 2240
    · have e : decide (y ≥ 2240) = false := decide_eq_false (by omega)
      rw [if_pos hy1, (hA x hx1).2 y hy1, e, Bool.false_and, Bool.or_false, el_pts]
    · have hyle : 2240 ≤ y := Nat.le_of_not_lt hy1
      have hy3 : y - 2240 < 6720 - 2240 := Nat.sub_lt_sub_right hyle hy
      have hy2 : y - 2240 < 4480 := hy3
      have e : decide (y ≥ 2240) = true := decide_eq_true hyle
      rw [if_neg hy1, el_tb_false (m := 2240) (hA x hx1).1 hyle,
        (hS x hx1).2 (y - 2240) hy2, e, Bool.true_and, Bool.false_or]
  · have hj : x - 2240 < 4480 := by omega
    rw [el_rowOf_sol hx1, if_neg hx1, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hy1 : y < 2240
    · have e : decide (y ≥ 2240) = false := decide_eq_false (by omega)
      rw [if_pos hy1, (hM _ hj).2 y hy1, e]
      simp only [Bool.false_and, Bool.or_false]
    · have hxle : 2240 ≤ x := Nat.le_of_not_lt hx1
      have hyle : 2240 ≤ y := Nat.le_of_not_lt hy1
      have hy3 : y - 2240 < 6720 - 2240 := Nat.sub_lt_sub_right hyle hy
      have hy2 : y - 2240 < 4480 := hy3
      have e : decide (y ≥ 2240) = true := decide_eq_true hyle
      have e2 : (x - 2240 != y - 2240) = (x != y) := by
        by_cases e3 : x = y
        · subst e3
          rw [bne_self_eq_false, bne_self_eq_false]
        · have e4 : x - 2240 ≠ y - 2240 := fun h => e3 (by
            rw [← Nat.sub_add_cancel hxle, h, Nat.sub_add_cancel hyle])
          rw [bne_iff_ne.mpr e3, bne_iff_ne.mpr e4]
      rw [if_neg hy1, el_tb_false (m := 2240) (hM _ hj).1 hyle,
        (hT _ hj).2 (y - 2240) hy2, e, Bool.true_and, Bool.false_or, e2]

theorem el_row {A S M TF NL : Nat → Nat} {F : Array (Array Nat)}
    (hA : ∀ i < 2240, A i < 2 ^ 2240 ∧
      ∀ i' < 2240, Nat.testBit (A i) i' = ptAdjC (ptCodes ())[i]! (ptCodes ())[i']!)
    (hS : ∀ i < 2240, S i < 2 ^ 4480 ∧
      ∀ j < 4480, Nat.testBit (S i) j = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hM : ∀ j < 4480, M j < 2 ^ 2240 ∧
      ∀ i < 2240, Nat.testBit (M j) i = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hT : ∀ j < 4480, TF j < 2 ^ 4480 ∧
      ∀ j' < 4480, Nat.testBit (TF j) j' = (j != j' && triTest (mkTabs (ptCodes ()) F) j j'))
    {x : Nat} (hx : x < 6720) (h : rowV A S M TF NL x = true) :
    (nbOf (mkTabs (ptCodes ()) F))[x]! =
      ((List.range (degK x)).map fun i => nbAt (NL x) (0 + i)).toArray := by
  simp only [rowV, el_strictB, el_bAnd, Bool.and_eq_true] at h
  obtain ⟨hb, hp, hs⟩ := el_walk _ _ _ _ _ _ h.2
  generalize hys : (List.range (degK x)).map (fun i => nbAt (NL x) (0 + i)) = ys at hb hp hs ⊢
  have hlen : ys.length = degK x := by rw [← hys, List.length_map, List.length_range]
  have hR : (ys.map fun y => 2 ^ y).sum = rowOf A S M TF x := by
    have e1 : Nat.shiftLeft (rowOf A S M TF x) (nat_lit 64) = 2 ^ 64 * rowOf A S M TF x := by
      rw [Nat.mul_comm]
      exact Nat.shiftLeft_eq _ _
    rw [e1, el_sum, hlen] at hs
    simp only [Nat.add_eq] at hs
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos 64) (by omega)
  have hmem : ∀ y, y ∈ ys ↔ y < 6720 ∧ adjT (mkTabs (ptCodes ()) F) x y := by
    intro y
    constructor
    · intro hy
      have hy6 := (hb y hy).2
      refine ⟨hy6, ?_⟩
      rw [← el_rowbit hA hS hM hT hx hy6, ← hR, el_bits ys hp]
      exact decide_eq_true hy
    · rintro ⟨hy6, hadj⟩
      rw [← el_rowbit hA hS hM hT hx hy6, ← hR, el_bits ys hp] at hadj
      exact of_decide_eq_true hadj
  have hx' : x < (Array.range 6720).size := by
    rw [Array.size_range]
    exact hx
  unfold nbOf
  rw [getElem!_pos _ x (by rw [Array.size_map]; exact hx'), Array.getElem_map,
    Array.getElem_range]
  apply Array.toList_inj.mp
  rw [Array.toList_filter, Array.toList_range, List.toList_toArray]
  apply el_eq_of_mem (List.pairwise_lt_range.filter _) hp
  intro y
  rw [List.mem_filter, List.mem_range, hmem]

theorem elimK_sound {F : Array (Array Nat)} {A S M TF NL RC : Nat → Nat} {T : Nat}
    (hA : ∀ i < 2240, A i < 2 ^ 2240 ∧
      ∀ i' < 2240, Nat.testBit (A i) i' = ptAdjC (ptCodes ())[i]! (ptCodes ())[i']!)
    (hS : ∀ i < 2240, S i < 2 ^ 4480 ∧
      ∀ j < 4480, Nat.testBit (S i) j = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hM : ∀ j < 4480, M j < 2 ^ 2240 ∧
      ∀ i < 2240, Nat.testBit (M j) i = ((mkTabs (ptCodes ()) F).inc[j]!)[i]!)
    (hT : ∀ j < 4480, TF j < 2 ^ 4480 ∧
      ∀ j' < 4480, Nat.testBit (TF j) j' = (j != j' && triTest (mkTabs (ptCodes ()) F) j j'))
    (hrow : ∀ x < 6720, rowV A S M TF NL x = true)
    (hel : ∀ x < 6720, elimV NL RC T x = true) :
    CFSG.KC.RankElim.ok 6720 (nbOf (mkTabs (ptCodes ()) F)) (fun x => parOf (trAt T x))
      (fun x => depOf (trAt T x)) (fun x k => rkOf (rcAt (RC x) k))
      (fun x k => apOf (rcAt (RC x) k)) (fun x k => bpOf (rcAt (RC x) k))
      (fun _ _ _ => true) = true := by
  have hnb : ∀ x < 6720, (nbOf (mkTabs (ptCodes ()) F))[x]! =
      ((List.range (degK x)).map fun i => nbAt (NL x) (0 + i)).toArray :=
    fun x hx => el_row hA hS hM hT hx (hrow x hx)
  generalize nbOf (mkTabs (ptCodes ()) F) = nb at hnb ⊢
  have hsz : ∀ x < 6720, (nb[x]!).size = degK x := by
    intro x hx
    rw [hnb x hx, List.size_toArray, List.length_map, List.length_range]
  have hget : ∀ x < 6720, ∀ k < degK x, (nb[x]!)[k]! = nbAt (NL x) k := by
    intro x hx k hk
    have hk' : k < ((List.range (degK x)).map fun i => nbAt (NL x) (0 + i)).toArray.size := by
      rw [List.size_toArray, List.length_map, List.length_range]
      exact hk
    rw [hnb x hx, getElem!_pos _ k hk']
    simp
  unfold CFSG.KC.RankElim.ok
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · intro x hx
    rw [List.mem_range] at hx
    have he := hel x hx
    simp only [elimV, treeK, el_strictB, el_bAnd, el_or, Bool.and_eq_true, Bool.or_eq_true,
      Nat.beq_eq, Nat.blt_eq] at he
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases he.1 with h0 | ⟨h1, h2, h3, h4, h5⟩
    · exact Or.inl h0
    · refine Or.inr ⟨⟨h1, h2⟩, ?_⟩
      unfold CFSG.Sporadic.SuzRecog.ElimCert.adjB CFSG.Sporadic.SuzRecog.ElimCert.occB
      simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, List.any_eq_true, List.mem_range,
        beq_iff_eq]
      refine ⟨el_ne h5, Or.inr ⟨pposOf (trAt T x), ?_, ?_⟩⟩
      · rw [hsz x hx]
        exact h3
      · rw [hget x hx _ h3]
        exact h4
  · intro x hx
    rw [List.mem_range] at hx
    rw [List.all_eq_true]
    intro k hk
    rw [List.mem_range, hsz x hx] at hk
    have he := hel x hx
    simp only [elimV, el_strictB, el_bAnd, Bool.and_eq_true] at he
    have hl := allBlk_get he.2 k hk
    rw [el_zero_add] at hl
    simp only [listK, el_strictB, el_bAnd, el_or] at hl
    unfold CFSG.KC.RankElim.listOK
    simp only [hget x hx k hk]
    cases hr : Nat.beq (rkOf (rcAt (RC x) k)) (nat_lit 0)
    · simp only [hr, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hl
      obtain ⟨ha, hz, hxz, hzy, hra, hb, hby, hrb⟩ := hl
      have hpos : 0 < rkOf (rcAt (RC x) k) := by
        apply Nat.pos_of_ne_zero
        intro e
        rw [e] at hr
        exact Bool.false_ne_true (hr.symm.trans (Nat.beq_refl 0))
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne,
        hsz x hx, hget x hx _ ha, hsz _ hz, hget _ hz _ hb, and_true]
      exact Or.inr ⟨⟨⟨⟨⟨⟨hpos, ha⟩, hz⟩, el_ne hxz⟩, el_ne hzy⟩, hra⟩, Or.inl ⟨⟨hb, hby⟩, hrb⟩⟩
    · simp only [hr, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at hl
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact Or.inl (Or.inr ⟨Nat.eq_of_beq_eq_true hr, hl⟩)

end CFSG.KC.D4Q2K

end
