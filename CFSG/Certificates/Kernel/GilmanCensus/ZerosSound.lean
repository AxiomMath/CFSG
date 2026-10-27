module

public import CFSG.Certificates.Kernel.GilmanCensus.RelSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

@[expose] def f3v (b1 b2 : Bool) : Nat := if b1 then 1 else if b2 then 2 else 0

@[expose] def okAt (a : Nat × Nat) (i : Nat) : Prop := ¬(a.1.testBit i = true ∧ a.2.testBit i = true)

@[expose] def valAt (a : Nat × Nat) (i : Nat) : Nat := f3v (a.1.testBit i) (a.2.testBit i)

theorem full_testBit (N i : Nat) : ((1 <<< N) - 1).testBit i = decide (i < N) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]

theorem addS_bits (full i : Nat) (hf : full.testBit i = true) (a b : Nat × Nat)
    (ha : okAt a i) (hb : okAt b i) :
    okAt (addS full a b) i ∧ valAt (addS full a b) i = (valAt a i + valAt b i) % 3 := by
  unfold okAt at *
  unfold valAt
  simp only [addS, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hf]
  generalize a.1.testBit i = x1 at *
  generalize a.2.testBit i = x2 at *
  generalize b.1.testBit i = y1 at *
  generalize b.2.testBit i = y2 at *
  cases x1 <;> cases x2 <;> cases y1 <;> cases y2 <;> simp_all [f3v]

theorem addS_high (full i : Nat) (hf : full.testBit i = false) (a b : Nat × Nat)
    (ha1 : a.1.testBit i = false) (ha2 : a.2.testBit i = false) :
    (addS full a b).1.testBit i = false ∧ (addS full a b).2.testBit i = false := by
  simp only [addS, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hf, ha1, ha2]
  cases b.1.testBit i <;> cases b.2.testBit i <;> simp

theorem smulS_bits (s i : Nat) (a : Nat × Nat) (ha : okAt a i) :
    okAt (smulS s a) i ∧ valAt (smulS s a) i = (s * valAt a i) % 3 := by
  unfold okAt at *
  unfold valAt
  unfold smulS
  have h3 : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
  rw [Nat.mul_mod]
  rcases h3 with h | h | h
  · simp only [h, BEq.rfl, ↓reduceIte, Nat.zero_testBit, f3v]
    simp
  · have e0 : (s % 3 == 0) = false := by rw [h]; rfl
    simp only [e0, h, BEq.rfl, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ha, ?_⟩
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp_all [f3v]
  · have e0 : (s % 3 == 0) = false := by rw [h]; rfl
    have e1 : (s % 3 == 1) = false := by rw [h]; rfl
    simp only [e0, e1, h, Bool.false_eq_true, ↓reduceIte]
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp_all [f3v]

theorem f3v_lt (b1 b2 : Bool) : f3v b1 b2 < 3 := by
  cases b1 <;> cases b2 <;> simp [f3v]

theorem fold_lo (full i : Nat) (hf : full.testBit i = true) :
    ∀ (v : List Nat) (P : List (Nat × Nat)) (r : List Nat) (acc : Nat × Nat), okAt acc i →
      P.length = r.length → (∀ c (h : c < P.length), okAt P[c] i) →
      (∀ c (h : c < P.length) (h' : c < r.length), valAt P[c] i = r[c]) →
      okAt ((List.zip v P).foldl (fun acc p => addS full acc (smulS p.1 p.2)) acc) i ∧
        valAt ((List.zip v P).foldl (fun acc p => addS full acc (smulS p.1 p.2)) acc) i =
          (valAt acc i + dotS v r) % 3
  | [], _, _, acc, hacc, _, _, _ => by
    refine ⟨by simpa using hacc, ?_⟩
    simp only [List.zip_nil_left, List.foldl_nil, dotS, Nat.add_zero]
    have : valAt acc i < 3 := f3v_lt _ _
    omega
  | _ :: _, [], r, acc, hacc, hl, _, _ => by
    have : r = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst this
    refine ⟨by simpa using hacc, ?_⟩
    simp only [List.zip_nil_right, List.foldl_nil, dotS, Nat.add_zero]
    have : valAt acc i < 3 := f3v_lt _ _
    omega
  | _ :: _, _ :: _, [], _, _, hl, _, _ => by simp at hl
  | s :: v, p :: P, x :: r, acc, hacc, hl, hok, hval => by
    have hp : okAt p i := hok 0 (by simp)
    have hx : valAt p i = x := hval 0 (by simp) (by simp)
    obtain ⟨hs1, hs2⟩ := smulS_bits s i p hp
    obtain ⟨ha1, ha2⟩ := addS_bits full i hf acc (smulS s p) hacc hs1
    rw [List.zip_cons_cons, List.foldl_cons]
    obtain ⟨h1, h2⟩ := fold_lo full i hf v P r _ ha1 (by simpa using hl)
      (fun c h => by
        have := hok (c + 1) (by simp; omega)
        rwa [List.getElem_cons_succ] at this)
      (fun c h h' => by
        have := hval (c + 1) (by simp; omega) (by simp; omega)
        rwa [List.getElem_cons_succ, List.getElem_cons_succ] at this)
    refine ⟨h1, ?_⟩
    rw [h2, ha2, hs2, hx, dotS]
    generalize s * x = t
    generalize dotS v r = D
    generalize valAt acc i = A
    omega

theorem fold_hi (full i : Nat) (hf : full.testBit i = false) :
    ∀ (Q : List (Nat × Nat × Nat)) (acc : Nat × Nat), acc.1.testBit i = false →
      acc.2.testBit i = false →
      (Q.foldl (fun acc p => addS full acc (smulS p.1 p.2)) acc).1.testBit i = false ∧
        (Q.foldl (fun acc p => addS full acc (smulS p.1 p.2)) acc).2.testBit i = false
  | [], _, h1, h2 => ⟨h1, h2⟩
  | q :: Q, acc, h1, h2 => by
    obtain ⟨e1, e2⟩ := addS_high full i hf acc (smulS q.1 q.2) h1 h2
    exact fold_hi full i hf Q _ e1 e2

theorem planeOf_go (c e j : Nat) : ∀ (F : List (List Nat)) (k m : Nat),
    ((F.zip (List.range' k F.length)).foldl
      (fun m p => if p.1.getD c 0 == e then m ||| bitK p.2 else m) m).testBit j =
      (m.testBit j || (decide (k ≤ j) && (F.getD (j - k) []).getD c 0 == e &&
        decide (j < k + F.length)))
  | [], k, m => by
    by_cases hk : k ≤ j
    · have hk2 : ¬ j < k := by omega
      simp [hk2]
    · simp [hk]
  | r :: F, k, m => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.foldl_cons,
      planeOf_go c e j F (k + 1)]
    have hstep : (if (r, k).1.getD c 0 == e then m ||| bitK k else m).testBit j =
        (m.testBit j || (decide (j = k) && r.getD c 0 == e)) := by
      split
      · rename_i he
        rw [Nat.testBit_or, bitK, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
        simp only at he
        rw [he, Bool.and_true]
        by_cases hjk : j = k
        · simp [hjk]
        · simp [hjk, Ne.symm hjk]
      · rename_i he
        have hX : (r.getD c 0 == e) = false := Bool.eq_false_iff.mpr he
        rw [hX, Bool.and_false, Bool.or_false]
    rw [hstep]
    rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · have a1 : decide (j = k) = false := by simp; omega
      have a2 : decide (k + 1 ≤ j) = false := by simp; omega
      have a3 : decide (k ≤ j) = false := by simp; omega
      simp [a1, a2, a3]
    · subst hjk
      have a2 : decide (j + 1 ≤ j) = false := by simp
      simp [a2]
    · have a1 : decide (j = k) = false := by simp; omega
      have a2 : decide (k + 1 ≤ j) = true := by simp; omega
      have a3 : decide (k ≤ j) = true := by simp; omega
      obtain ⟨t, ht⟩ : ∃ t, j - k = t + 1 := ⟨j - k - 1, by omega⟩
      have ht' : j - (k + 1) = t := by omega
      rw [a1, a2, a3, ht, ht', List.getD_cons_succ]
      have e4 : decide (j < k + 1 + F.length) = decide (j < k + (F.length + 1)) := by
        congr 1
        apply propext
        omega
      rw [e4]
      simp

theorem planeOf_testBit (F : List (List Nat)) (c e j : Nat) :
    (planeOf F c e).testBit j = (decide (j < F.length) && (F.getD j []).getD c 0 == e) := by
  unfold planeOf
  rw [List.range_eq_range', planeOf_go]
  simp only [Nat.zero_testBit, Bool.false_or, Nat.zero_le, decide_true, Bool.true_and,
    Nat.sub_zero, Nat.zero_add]
  rw [Bool.and_comm]

theorem foldBits (p : Nat → Bool) (j : Nat) : ∀ (n k m : Nat),
    ((List.range' k n).foldl (fun m i => if p i = true then m ||| bitK i else m) m).testBit j =
      (m.testBit j || (decide (k ≤ j) && decide (j < k + n) && p j))
  | 0, k, m => by
    by_cases hk : k ≤ j
    · have hk2 : ¬ j < k := by omega
      simp [hk2]
    · simp [hk]
  | n + 1, k, m => by
    rw [List.range'_succ, List.foldl_cons, foldBits p j n (k + 1)]
    have hstep : (if p k = true then m ||| bitK k else m).testBit j =
        (m.testBit j || (decide (j = k) && p k)) := by
      split
      · rename_i he
        rw [Nat.testBit_or, bitK, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, he,
          Bool.and_true]
        by_cases hjk : j = k
        · simp [hjk]
        · simp [hjk, Ne.symm hjk]
      · rename_i he
        have hX : p k = false := Bool.eq_false_iff.mpr he
        rw [hX, Bool.and_false, Bool.or_false]
    rw [hstep]
    rcases Nat.lt_trichotomy j k with hjk | hjk | hjk
    · have a1 : decide (j = k) = false := by simp; omega
      have a2 : decide (k + 1 ≤ j) = false := by simp; omega
      have a3 : decide (k ≤ j) = false := by simp; omega
      simp [a1, a2, a3]
    · subst hjk
      have a2 : decide (j + 1 ≤ j) = false := by simp
      have a3 : decide (j < j + (n + 1)) = true := by simp
      simp [a2, a3]
    · have a1 : decide (j = k) = false := by simp; omega
      have a2 : decide (k + 1 ≤ j) = true := by simp; omega
      have a3 : decide (k ≤ j) = true := by simp; omega
      have e4 : decide (j < k + 1 + n) = decide (j < k + (n + 1)) := by
        congr 1
        apply propext
        omega
      rw [a1, a2, a3, e4]
      simp

theorem zerosL_testBit (dk : DK) (v : List Nat) (j : Nat) :
    (zerosL dk v).testBit j = (decide (j < dk.N) && dot3K v (fK dk j) == 0) := by
  unfold zerosL
  rw [foldBits (fun i => dot3K v (fK dk i) == 0) j dk.N 0 0]
  simp

theorem fin_bit (b1 b2 : Bool) (h : ¬(b1 = true ∧ b2 = true)) :
    (true ^^ (b1 || b2)) = (f3v b1 b2 == 0) := by
  cases b1 <;> cases b2 <;> simp_all [f3v]

theorem zerosK_eq (dk : DK) (hz : zpOkK dk = true) (hlen : ∀ r ∈ dk.F, r.length = dk.d)
    (h3 : ∀ r ∈ dk.F, ∀ x ∈ r, x < 3) (v : List Nat) : zerosK dk v = zerosL dk v := by
  simp only [zpOkK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hz
  obtain ⟨⟨⟨⟨_, hFN⟩, _⟩, hzl⟩, hzp⟩ := hz
  apply Nat.eq_of_testBit_eq
  intro j
  rw [zerosL_testBit]
  simp only [zerosK, DK.full]
  rw [Nat.testBit_xor, Nat.testBit_or, full_testBit]
  by_cases hj : j < dk.N
  · have hf : ((1 <<< dk.N) - 1).testBit j = true := by rw [full_testBit]; simpa using hj
    have hjF : j < dk.F.length := by omega
    have hrow : fK dk j ∈ dk.F := by
      rw [fK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjF]
      exact List.getElem_mem _
    have hrl : (fK dk j).length = dk.d := hlen _ hrow
    have hP : ∀ c (h : c < dk.zp.length),
        dk.zp[c] = (planeOf dk.F c 1, planeOf dk.F c 2) := by
      intro c h
      have := hzp c (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] at this
      exact this
    have hok : ∀ c (h : c < dk.zp.length), okAt dk.zp[c] j := by
      intro c h
      rw [hP c h]
      unfold okAt
      simp only [planeOf_testBit, hjF, decide_true, Bool.true_and, beq_iff_eq]
      omega
    have hval : ∀ c (h : c < dk.zp.length) (h' : c < (fK dk j).length),
        valAt dk.zp[c] j = (fK dk j)[c] := by
      intro c h h'
      rw [hP c h]
      unfold valAt
      simp only [planeOf_testBit, hjF, decide_true, Bool.true_and]
      have hx : (fK dk j)[c] < 3 := h3 _ hrow _ (List.getElem_mem _)
      have hg : (dk.F.getD j []).getD c 0 = (fK dk j)[c] := by
        rw [← fK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h']
        rfl
      rw [hg]
      generalize (fK dk j)[c] = x at hx
      rcases (by omega : x = 0 ∨ x = 1 ∨ x = 2) with rfl | rfl | rfl <;> rfl
    obtain ⟨h1, h2⟩ := fold_lo ((1 <<< dk.N) - 1) j hf v dk.zp (fK dk j) (0, 0) (by simp [okAt])
      (by omega) hok hval
    have h0 : valAt ((0, 0) : Nat × Nat) j = 0 := by simp [valAt, f3v]
    rw [h0, Nat.zero_add] at h2
    revert h1 h2
    unfold okAt valAt dot3K
    generalize (List.foldl (fun acc p => addS ((1 <<< dk.N) - 1) acc (smulS p.1 p.2)) (0, 0)
      (v.zip dk.zp)) = s
    intro h1 h2
    rw [← h2, decide_eq_true hj, Bool.true_and]
    exact fin_bit _ _ h1
  · have hf : ((1 <<< dk.N) - 1).testBit j = false := by rw [full_testBit]; simpa using hj
    obtain ⟨h1, h2⟩ := fold_hi ((1 <<< dk.N) - 1) j hf (List.zip v dk.zp) (0, 0) (by simp)
      (by simp)
    rw [h1, h2, decide_eq_false hj]
    rfl

theorem zerosOf_eq_K {dt : Data} {dk : DK} (h : Rel dt dk) (hz : zpOkK dk = true)
    (h3 : ∀ r ∈ dk.F, ∀ x ∈ r, x < 3) (v : Array Nat) :
    zerosOf dt v = zerosK dk v.toList := by
  rw [zerosOf_eq h, zerosK_eq dk hz _ h3]
  intro r hr
  rw [← h.F, LL] at hr
  simp only [List.mem_map] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  rw [Array.length_toList, h.Fsz a ha, h.d]

end Certificates.GilmanCensusK

end
