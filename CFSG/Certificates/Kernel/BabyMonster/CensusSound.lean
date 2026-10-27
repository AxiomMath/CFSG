module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Census
public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbitList
public import Certificates.Data.CFSGNative.MonsterB.Max2Tower
import CFSG.Certificates.Kernel.BabyMonster.VStripSound
import CFSG.Certificates.Kernel.BabyMonster.Q23Sound
import Mathlib.Data.Int.Star

public section

namespace CFSG.KC.BM

open CFSG.Monster.B.CTIB.Kernel

inductive AllRanges (LB DT : List (List Nat)) (Ts reps : List Nat) (len cnt : Nat) :
    List Nat → Nat → Nat → Prop
  | nil (hi : Nat) : AllRanges LB DT Ts reps len cnt [] hi hi
  | cons (c lo hi : Nat) (cs : List Nat) :
      Nat.beq (censusRange LB DT Ts reps lo len cnt) c = true →
      AllRanges LB DT Ts reps len cnt cs (lo + len) hi →
      AllRanges LB DT Ts reps len cnt (c :: cs) lo hi

@[expose] noncomputable def actPair (M0 M1 : Nat) (k v : Nat) : Nat :=
  if k = 0 then vm32 22 M0 v else vm32 22 M1 v

@[expose] def censusValid22 (v : Nat) : Bool := decide (0 < v) && decide (v < 2 ^ 22)

@[expose] noncomputable def rowsEq22 (M : Nat) (rows : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB ih (Nat.beq (vm32 (nat_lit 22) M (Nat.shiftLeft (nat_lit 1) i)) (nthN rows i)))
    (nat_lit 22)

private theorem andRec_spec {f : Nat → Bool} : ∀ {k : Nat},
    Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) k = true → ∀ i < k, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, h, i, hi => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB ih (f i)) k) (f k) =
        true := h
    rw [CFSG.KC.BM.SL.andB_eq, Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact andRec_spec h'.1 i hi
    · exact h'.2

private theorem nthN_getD : ∀ (L : List Nat) (i : Nat), nthN L i = L.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, i + 1 => nthN_getD L i

open CFSG.KC.BM.SL in
private theorem actGo_bit (rows : Array Nat) (v j : Nat) : ∀ (i acc : Nat),
    bz ((CFSG.Monster.VisCert.Native.actGo rows v i acc).testBit j) = bz (acc.testBit j) +
      ∑ l ∈ Finset.range i, bz (v.testBit l) * bz (rows[l]!.testBit j)
  | 0, acc => by simp [CFSG.Monster.VisCert.Native.actGo]
  | i + 1, acc => by
    rw [CFSG.Monster.VisCert.Native.actGo, actGo_bit rows v j i, Finset.sum_range_succ]
    cases hv : v.testBit i
    · simp
    · simp only [ite_true, Nat.testBit_xor, bz_xor, bz_true, one_mul]
      ring

open CFSG.KC.BM.SL in
private theorem vm32_pow (M i j : Nat) (hi : i < 22) (hj : j < 32) :
    bz ((vm32 22 M (2 ^ i)).testBit j) = bz ((Nat.shiftRight M (32 * i)).testBit j) := by
  rw [← ite_bz, vm32_bit 22 M (2 ^ i) hj, Finset.sum_eq_single i]
  · simp [Nat.testBit_two_pow_self, ite_bz]
  · intro l _ hl
    simp [Ne.symm hl]
  · intro h
    exact absurd (Finset.mem_range.2 hi) h

open CFSG.KC.BM.SL in
theorem vm32_eq_act22 {M : Nat} {rows : Array Nat} (h : rowsEq22 M rows.toList = true) :
    ∀ v < 2 ^ 22, vm32 22 M v = CFSG.Monster.B.Max2.Native.act22 rows v := by
  have hr : ∀ i < 22, rows[i]! = vm32 22 M (2 ^ i) := fun i hi => by
    have := Nat.eq_of_beq_eq_true (andRec_spec (f := fun i => Nat.beq (vm32 (nat_lit 22) M
      (Nat.shiftLeft (nat_lit 1) i)) (nthN rows.toList i)) h i hi)
    rw [nthN_getD, nshl, Nat.shiftLeft_eq, Nat.one_mul] at this
    have e2 : rows.toList.getD i 0 = rows[i]! := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
      cases rows[i]? <;> rfl
    rw [← e2]
    exact this.symm
  intro v _
  apply Nat.eq_of_testBit_eq
  intro j
  unfold CFSG.Monster.B.Max2.Native.act22
  apply bz_inj
  rw [actGo_bit, Nat.zero_testBit, bz_false, zero_add]
  by_cases hj : j < 32
  · rw [← ite_bz, vm32_bit 22 M v hj]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [hr l hl, vm32_pow M l j hl hj, ite_bz, ite_bz]
  · have hz : ∀ x : Nat, x < 2 ^ 32 → x.testBit j = false := fun x hx =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [hz _ (vm32_lt 22 M v), bz_false]
    symm
    apply Finset.sum_eq_zero
    intro l hl
    rw [Finset.mem_range] at hl
    rw [hr l hl, hz _ (vm32_lt 22 M _), bz_false, mul_zero]

private noncomputable def vec22 (v : Nat) : Fin 22 → ZMod 2 := fun i => bz2 (v.testBit i)

private theorem bz2_inj {a b : Bool} (h : bz2 a = bz2 b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private theorem vec22_vm32 {M : Nat} (v : Nat) :
    vec22 (vm32 22 M v) = Matrix.vecMul (vec22 v) (mat32 M) := by
  funext j
  have hj : j.val < 32 := by omega
  have e : vm32 22 M v = vmLoop 22 M v 0 := rfl
  have e0 : bz2 false = 0 := rfl
  unfold vec22
  rw [e, vmLoop_bit _ _ _ _ hj, Nat.zero_testBit, e0, zero_add, Matrix.vecMul, dotProduct,
    Finset.sum_range]
  refine Finset.sum_congr rfl fun l _ => ?_
  change _ = bz2 _ * bz2 ((fld32 M l).testBit j)
  rw [testBit_fld32 _ _ _ hj, Nat.testBit_shiftRight, Nat.add_comm]

private theorem vec22_xor (a b : Nat) : vec22 (a ^^^ b) = vec22 a + vec22 b := by
  funext i
  unfold vec22
  rw [Nat.testBit_xor, bz2_xor]
  rfl

private theorem vec22_zero : vec22 0 = 0 := by
  funext i
  unfold vec22
  rw [Nat.zero_testBit]
  rfl

private theorem eq_of_vec22 {a b : Nat} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22) (h : vec22 a = vec22 b) :
    a = b :=
  Nat.eq_of_testBit_eq fun j => by
    by_cases hj : j < 22
    · exact bz2_inj (congrFun h ⟨j, hj⟩)
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega)))]

private abbrev WF (M : Nat) : Prop := ∀ l < 22, fld32 M l < 2 ^ 22

private theorem vm32_xor {M : Nat} (hM : WF M) (a b : Nat) :
    vm32 22 M (a ^^^ b) = vm32 22 M a ^^^ vm32 22 M b :=
  eq_of_vec22 (vm32_lt22 hM _) (Nat.xor_lt_two_pow (vm32_lt22 hM _) (vm32_lt22 hM _)) (by
    rw [vec22_vm32, vec22_xor, Matrix.add_vecMul, vec22_xor, vec22_vm32, vec22_vm32])

private theorem vm32_inv {M N : Nat} (hN : WF N) (h : mat32 M * mat32 N = 1) {v : Nat}
    (hv : v < 2 ^ 22) : vm32 22 N (vm32 22 M v) = v :=
  eq_of_vec22 (vm32_lt22 hN _) hv (by
    rw [vec22_vm32, vec22_vm32, Matrix.vecMul_vecMul, h, Matrix.vecMul_one])

private theorem vm32_zero {M : Nat} (hM : WF M) : vm32 22 M 0 = 0 :=
  eq_of_vec22 (vm32_lt22 hM _) (by decide) (by rw [vec22_vm32, vec22_zero, Matrix.zero_vecMul])

private theorem vm32_ne {M N : Nat} (hN : WF N) (h : mat32 M * mat32 N = 1) {v : Nat}
    (hv : v < 2 ^ 22) (h0 : v ≠ 0) : vm32 22 M v ≠ 0 := fun e => by
  have := vm32_inv hN h hv
  rw [e, vm32_zero hN] at this
  exact h0 this.symm

private theorem split22 (v : Nat) :
    v = (v &&& 255) ^^^ ((((v >>> 8) &&& 255) <<< 8) ^^^ ((v >>> 16) <<< 16)) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
  rw [e255, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h1 : j < 8
  · have a1 : ¬ 8 ≤ j := by omega
    have a2 : ¬ 16 ≤ j := by omega
    simp [h1, a1, a2]
  · by_cases h2 : j < 16
    · have a1 : 8 ≤ j := by omega
      have a2 : j - 8 < 8 := by omega
      have a3 : ¬ 16 ≤ j := by omega
      have e : 8 + (j - 8) = j := by omega
      simp [h1, a1, a2, a3, e]
    · have a1 : 8 ≤ j := by omega
      have a2 : ¬ j - 8 < 8 := by omega
      have a3 : 16 ≤ j := by omega
      have e : 16 + (j - 16) = j := by omega
      simp [h1, a1, a2, a3, e]

private theorem byteTab_spec {M p T : Nat} (h : byteTabOK M p T = true) :
    ∀ b < Bool.rec (motive := fun _ => Nat) (nat_lit 256) (nat_lit 64) (Nat.beq p (nat_lit 2)),
      fld32 T b = vm32 22 M (b <<< (8 * p)) := fun b hb =>
  Nat.eq_of_beq_eq_true (andRec_spec (f := fun b => Nat.beq (fld32 T b)
    (vm32 (nat_lit 22) M (Nat.shiftLeft b (Nat.mul (nat_lit 8) p)))) h b hb)

private theorem mulT_eq {Ts : List Nat} {M k : Nat} (hM : WF M)
    (h0 : byteTabOK M 0 (nthN Ts (3 * k)) = true) (h1 : byteTabOK M 1 (nthN Ts (3 * k + 1)) = true)
    (h2 : byteTabOK M 2 (nthN Ts (3 * k + 2)) = true) {v : Nat} (hv : v < 2 ^ 22) :
    mulT Ts k v = vm32 22 M v := by
  have hb0 : v &&& 255 < 256 := Nat.and_lt_two_pow (n := 8) _ (by decide)
  have hb1 : (v >>> 8) &&& 255 < 256 := Nat.and_lt_two_pow (n := 8) _ (by decide)
  have hb2 : v >>> 16 < 64 := by
    rw [Nat.shiftRight_eq_div_pow]
    have e1 : (2 : Nat) ^ 16 = 65536 := rfl
    have e2 : (2 : Nat) ^ 22 = 4194304 := rfl
    rw [e1]
    rw [e2] at hv
    omega
  change Nat.xor (fld32 (nthN Ts (3 * k)) (Nat.land v 255))
    (Nat.xor (fld32 (nthN Ts (3 * k + 1)) (Nat.land (Nat.shiftRight v 8) 255))
      (fld32 (nthN Ts (3 * k + 2)) (Nat.shiftRight v 16))) = _
  rw [SL.nxor, SL.nxor, SL.nland, SL.nland, SL.nshr, SL.nshr, byteTab_spec h0 _ hb0,
    byteTab_spec h1 _ hb1, byteTab_spec h2 _ hb2, Nat.mul_zero, Nat.shiftLeft_zero, Nat.mul_one,
    ← vm32_xor hM, ← vm32_xor hM, ← split22 v]

@[expose] noncomputable def noFailL (cs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (notB (Nat.beq c cnFail)) ih) cs

private theorem noFailL_spec : ∀ {cs : List Nat}, noFailL cs = true → ∀ c ∈ cs, c ≠ cnFail
  | [], _, c, hc => absurd hc List.not_mem_nil
  | c' :: cs, h, c, hc => by
    have h' : andB (notB (Nat.beq c' cnFail)) (noFailL cs) = true := h
    rw [SL.andB_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · intro e
      rw [e, Nat.beq_refl] at h'
      exact absurd h'.1 (by decide)
    · exact noFailL_spec h'.2 c hc

private theorem brec_ne {c : Bool} {e t : Nat} (h : Bool.rec (motive := fun _ => Nat) e t c ≠ e) :
    c = true ∧ Bool.rec (motive := fun _ => Nat) e t c = t := by
  cases c
  · exact absurd rfl h
  · exact ⟨rfl, rfl⟩

private theorem brecB {c t e : Bool} (h : Bool.rec (motive := fun _ => Bool) e t c = true) :
    (c = true → t = true) ∧ (c = false → e = true) := by
  cases c
  · exact ⟨fun h' => absurd h' (by decide), fun _ => h⟩
  · exact ⟨fun _ => h, fun h' => absurd h' (by decide)⟩

private def OneOK (LB DT : List (List Nat)) (Ts reps : List Nat) (v : Nat) : Prop :=
  0 < lookLB LB v ∧ lookLB LB (mulT Ts 0 v) = lookLB LB v ∧ lookLB LB (mulT Ts 1 v) = lookLB LB v ∧
    (Nat.shiftRight (lookDT DT v) 2 = 0 → v = nthN reps (lookLB LB v - 1)) ∧
    (Nat.shiftRight (lookDT DT v) 2 ≠ 0 →
      Nat.succ (Nat.shiftRight (lookDT DT (mulT Ts (Nat.xor (Nat.land (lookDT DT v) 3) 2) v)) 2) =
        Nat.shiftRight (lookDT DT v) 2)

private theorem censusOne_spec {LB DT : List (List Nat)} {Ts reps : List Nat} {v cnt : Nat}
    (h : censusOne LB DT Ts reps v cnt ≠ cnFail) :
    censusOne LB DT Ts reps v cnt = cnt + 2 ^ (24 * (lookLB LB v - 1)) ∧ OneOK LB DT Ts reps v := by
  unfold censusOne at h ⊢
  dsimp only at h ⊢
  obtain ⟨hc, he⟩ := brec_ne h
  refine ⟨?_, ?_⟩
  · rw [he, SL.nadd, SL.nshl, Nat.shiftLeft_eq, Nat.one_mul]
    rfl
  · simp only [SL.andB_eq, Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hc
    rw [Nat.blt_eq] at h1
    obtain ⟨d1, d2⟩ := brecB h4
    refine ⟨h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, fun hz => ?_, fun hz => ?_⟩
    · exact Nat.eq_of_beq_eq_true (d1 (by rw [hz]; rfl))
    · refine Nat.eq_of_beq_eq_true (d2 ?_)
      cases e : Nat.beq (Nat.shiftRight (lookDT DT v) 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) hz

private noncomputable def incr (LB : List (List Nat)) (v : Nat) : Nat :=
  if v = 0 then 0 else 2 ^ (24 * (lookLB LB v - 1))

private theorem censusRange_spec {LB DT : List (List Nat)} {Ts reps : List Nat} :
    ∀ (len lo cnt : Nat), censusRange LB DT Ts reps lo len cnt ≠ cnFail →
      censusRange LB DT Ts reps lo len cnt = cnt + ((List.range' lo len).map (incr LB)).sum ∧
        ∀ v, lo ≤ v → v < lo + len → v ≠ 0 → OneOK LB DT Ts reps v
  | 0, lo, cnt, _ => ⟨by simp only [List.range'_zero, List.map_nil, List.sum_nil, Nat.add_zero]; rfl,
      fun v h1 h2 => by omega⟩
  | len + 1, lo, cnt, h => by
    have e : censusRange LB DT Ts reps lo (len + 1) cnt =
        forceB (Bool.rec (motive := fun _ => Nat) (censusOne LB DT Ts reps lo cnt) cnt (Nat.beq lo 0))
          (fun c' => Bool.rec (motive := fun _ => Nat)
            (forceB (Nat.succ lo) (fun v' => censusRange LB DT Ts reps v' len c')) cnFail
            (Nat.beq c' cnFail)) := rfl
    rw [e, forceB_q] at h ⊢
    generalize hc' : Bool.rec (motive := fun _ => Nat) (censusOne LB DT Ts reps lo cnt) cnt
      (Nat.beq lo 0) = c' at h ⊢
    cases hf : Nat.beq c' cnFail
    · simp only [hf] at h ⊢
      rw [forceB_q] at h ⊢
      obtain ⟨ih1, ih2⟩ := censusRange_spec len (lo + 1) c' h
      have hne : c' ≠ cnFail := fun e => by
        rw [e, Nat.beq_refl] at hf
        exact absurd hf (by decide)
      have hlo : c' = cnt + incr LB lo ∧ (lo ≠ 0 → OneOK LB DT Ts reps lo) := by
        by_cases h0 : lo = 0
        · subst h0
          have e0 : Nat.beq 0 0 = true := rfl
          rw [e0] at hc'
          exact ⟨by rw [← hc']; simp [incr], fun h => absurd rfl h⟩
        · have hb : Nat.beq lo 0 = false := by
            cases e : Nat.beq lo 0
            · rfl
            · exact absurd (Nat.eq_of_beq_eq_true e) h0
          rw [hb] at hc'
          have hc2 : censusOne LB DT Ts reps lo cnt = c' := hc'
          rw [← hc2] at hne
          obtain ⟨e1, e2⟩ := censusOne_spec hne
          refine ⟨?_, fun _ => e2⟩
          rw [← hc2, e1]
          simp [incr, h0]
      refine ⟨?_, fun v h1 h2 h3 => ?_⟩
      · rw [ih1, hlo.1, List.range'_succ, List.map_cons, List.sum_cons, Nat.add_assoc]
      · rcases Nat.eq_or_lt_of_le h1 with rfl | h1
        · exact hlo.2 h3
        · exact ih2 v (by omega) (by omega) h3
    · simp only [hf] at h
      exact absurd rfl h

private theorem allRanges_spec {LB DT : List (List Nat)} {Ts reps : List Nat} {cs : List Nat}
    {lo hi : Nat} (h : AllRanges LB DT Ts reps 4096 0 cs lo hi) :
    (∀ c ∈ cs, c ≠ cnFail) → lo ≤ hi ∧ cs.sum = ((List.range' lo (hi - lo)).map (incr LB)).sum ∧
      ∀ v, lo ≤ v → v < hi → v ≠ 0 → OneOK LB DT Ts reps v := by
  induction h with
  | nil hi => exact fun _ => ⟨Nat.le_refl _, by simp, fun v h1 h2 => by omega⟩
  | cons c lo hi cs h1 _ ih =>
    intro hf
    obtain ⟨a1, a2, a3⟩ := ih fun c' hc' => hf c' (List.mem_cons_of_mem _ hc')
    have hc := Nat.eq_of_beq_eq_true h1
    have hne : censusRange LB DT Ts reps lo 4096 0 ≠ cnFail := by
      rw [hc]
      exact hf c List.mem_cons_self
    obtain ⟨b1, b2⟩ := censusRange_spec 4096 lo 0 hne
    refine ⟨by omega, ?_, fun v hv1 hv2 hv3 => ?_⟩
    · have e : hi - lo = 4096 + (hi - (lo + 4096)) := by omega
      rw [List.sum_cons, ← hc, b1, a2, e, ← List.range'_append_1, List.map_append, List.sum_append,
        Nat.zero_add]
    · by_cases hv : v < lo + 4096
      · exact b2 v hv1 hv hv3
      · exact a3 v (by omega) hv2 hv3

private theorem field_count {L : Nat → Nat} (m : Nat) (l : List Nat) (hl : l.length < 2 ^ 24) :
    (l.map fun v => if v = 0 then 0 else 2 ^ (24 * (L v - 1))).sum / 2 ^ (24 * m) % 2 ^ 24 =
      (l.filter fun v => decide (v ≠ 0) && decide (L v - 1 = m)).length := by
  have key : ∀ l : List Nat, ∃ low high,
      (l.map fun v => if v = 0 then 0 else 2 ^ (24 * (L v - 1))).sum = low + 2 ^ (24 * m) *
        ((l.filter fun v => decide (v ≠ 0) && decide (L v - 1 = m)).length + 2 ^ 24 * high) ∧
      low * 2 ^ 24 ≤ l.length * 2 ^ (24 * m) := by
    intro l
    induction l with
    | nil => exact ⟨0, 0, by simp, by simp⟩
    | cons v l ih =>
      obtain ⟨low, high, e, hb⟩ := ih
      have hpos : 0 < 2 ^ (24 * m) := Nat.pow_pos (by omega)
      by_cases h0 : v = 0
      · refine ⟨low, high, ?_, ?_⟩
        · simp [h0, e]
        · simp only [List.length_cons]
          nlinarith
      · rcases Nat.lt_trichotomy (L v - 1) m with hlt | heq | hgt
        · refine ⟨2 ^ (24 * (L v - 1)) + low, high, ?_, ?_⟩
          · have hne : ¬ L v - 1 = m := by omega
            simp [h0, hne, e]
            ring
          · have : 2 ^ (24 * (L v - 1)) * 2 ^ 24 ≤ 2 ^ (24 * m) := by
              rw [← Nat.pow_add]
              exact Nat.pow_le_pow_right (by omega) (by omega)
            simp only [List.length_cons]
            nlinarith
        · refine ⟨low, high, ?_, ?_⟩
          · simp [h0, heq, e]
            ring
          · simp only [List.length_cons]
            nlinarith
        · refine ⟨low, high + 2 ^ (24 * (L v - 1 - m - 1)), ?_, ?_⟩
          · have hne : ¬ L v - 1 = m := by omega
            have ep : 2 ^ (24 * (L v - 1)) = 2 ^ (24 * m) * (2 ^ 24 * 2 ^ (24 * (L v - 1 - m - 1))) := by
              rw [← Nat.pow_add, ← Nat.pow_add]
              congr 1
              omega
            simp [h0, hne, e, ep]
            ring
          · simp only [List.length_cons]
            nlinarith
  obtain ⟨low, high, e, hb⟩ := key l
  have hpos : 0 < 2 ^ (24 * m) := Nat.pow_pos (by omega)
  have hlow : low < 2 ^ (24 * m) := by
    have : low * 2 ^ 24 < 2 ^ (24 * m) * 2 ^ 24 := by
      calc low * 2 ^ 24 ≤ l.length * 2 ^ (24 * m) := hb
        _ < 2 ^ 24 * 2 ^ (24 * m) := Nat.mul_lt_mul_of_pos_right hl hpos
        _ = 2 ^ (24 * m) * 2 ^ 24 := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right this
  have hmid : (l.filter fun v => decide (v ≠ 0) && decide (L v - 1 = m)).length < 2 ^ 24 :=
    Nat.lt_of_le_of_lt (List.length_filter_le _ _) hl
  rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmid]

private theorem mat_comm {A B : Matrix (Fin 22) (Fin 22) (ZMod 2)} (h : A * B = 1) : B * A = 1 :=
  (mul_eq_one_comm (M := Matrix (Fin 22) (Fin 22) (ZMod 2))).mp h

theorem census_sound {LB DT : List (List Nat)} {Ts reps cs : List Nat} {M0 M1 M2 M3 : Nat}
    (t00 : byteTabOK M0 0 (nthN Ts 0) = true) (t01 : byteTabOK M0 1 (nthN Ts 1) = true)
    (t02 : byteTabOK M0 2 (nthN Ts 2) = true) (t10 : byteTabOK M1 0 (nthN Ts 3) = true)
    (t11 : byteTabOK M1 1 (nthN Ts 4) = true) (t12 : byteTabOK M1 2 (nthN Ts 5) = true)
    (t20 : byteTabOK M2 0 (nthN Ts 6) = true) (t21 : byteTabOK M2 1 (nthN Ts 7) = true)
    (t22 : byteTabOK M2 2 (nthN Ts 8) = true) (t30 : byteTabOK M3 0 (nthN Ts 9) = true)
    (t31 : byteTabOK M3 1 (nthN Ts 10) = true) (t32 : byteTabOK M3 2 (nthN Ts 11) = true)
    (hinv : andB (Nat.beq (mm32 (nat_lit 22) M0 M2) (id32 (nat_lit 22)))
      (Nat.beq (mm32 (nat_lit 22) M1 M3) (id32 (nat_lit 22))) = true)
    (hwf : andB (wf32 (nat_lit 22) M0) (andB (wf32 (nat_lit 22) M1)
      (andB (wf32 (nat_lit 22) M2) (wf32 (nat_lit 22) M3))) = true)
    (hr : AllRanges LB DT Ts reps 4096 0 cs 0 4194304) (hcs : noFailL cs = true) {a : Nat}
    (ha : 1 ≤ a) (_ha' : a ≤ lenL reps)
    (hrep : andB (censusValid22 (nthN reps (a - 1))) (Nat.beq (lookLB LB (nthN reps (a - 1))) a) =
      true) :
    ∃ pts : List Nat, pts.length = cs.sum / 2 ^ (24 * (a - 1)) % 2 ^ 24 ∧ pts.Nodup ∧
      nthN reps (a - 1) ∈ pts ∧
      (∀ p ∈ pts, censusValid22 p = true ∧ lookLB LB p = a) ∧
      (∀ p ∈ pts, ∀ k < 2, actPair M0 M1 k p ∈ pts) ∧
      ∀ p ∈ pts, Reach (actPair M0 M1) 2 censusValid22 (nthN reps (a - 1)) p := by
  simp only [SL.andB_eq, Bool.and_eq_true] at hwf hinv hrep
  obtain ⟨w0, w1, w2, w3⟩ := hwf
  have f0 := wf_fields w0
  have f1 := wf_fields w1
  have f2 := wf_fields w2
  have f3 := wf_fields w3
  have i02 : mat32 M0 * mat32 M2 = 1 := by
    have e : mm32 22 M0 M2 = id32 22 := Nat.eq_of_beq_eq_true hinv.1
    rw [← mm32_mat, e, id32_mat]
  have i13 : mat32 M1 * mat32 M3 = 1 := by
    have e : mm32 22 M1 M3 = id32 22 := Nat.eq_of_beq_eq_true hinv.2
    rw [← mm32_mat, e, id32_mat]
  have i20 : mat32 M2 * mat32 M0 = 1 := mat_comm i02
  have i31 : mat32 M3 * mat32 M1 = 1 := mat_comm i13
  have m0 : ∀ v < 2 ^ 22, mulT Ts 0 v = vm32 22 M0 v := fun v hv => mulT_eq (k := 0) f0 t00 t01 t02 hv
  have m1 : ∀ v < 2 ^ 22, mulT Ts 1 v = vm32 22 M1 v := fun v hv => mulT_eq (k := 1) f1 t10 t11 t12 hv
  have m2 : ∀ v < 2 ^ 22, mulT Ts 2 v = vm32 22 M2 v := fun v hv => mulT_eq (k := 2) f2 t20 t21 t22 hv
  have m3 : ∀ v < 2 ^ 22, mulT Ts 3 v = vm32 22 M3 v := fun v hv => mulT_eq (k := 3) f3 t30 t31 t32 hv
  obtain ⟨-, hsum, hok⟩ := allRanges_spec hr (noFailL_spec hcs)
  have hok' : ∀ v, 0 < v → v < 2 ^ 22 → OneOK LB DT Ts reps v := fun v h1 h2 =>
    hok v (Nat.zero_le v) h2 (by omega)
  have hvalid : ∀ v, censusValid22 v = true ↔ 0 < v ∧ v < 2 ^ 22 := fun v => by
    simp [censusValid22]
  let pts := (List.range' 0 4194304).filter fun v => decide (v ≠ 0) && decide (lookLB LB v - 1 = a - 1)
  have hmem : ∀ p, p ∈ pts ↔ 0 < p ∧ p < 2 ^ 22 ∧ lookLB LB p = a := fun p => by
    simp only [pts, List.mem_filter, List.mem_range'_1, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨-, h2⟩, h3, h4⟩
      have h1 := (hok' p (by omega) h2).1
      exact ⟨by omega, h2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨Nat.zero_le p, h2⟩, by omega, by omega⟩
  have hlab0 : ∀ v, 0 < v → v < 2 ^ 22 → lookLB LB (vm32 22 M0 v) = lookLB LB v := fun v h1 h2 => by
    rw [← m0 v h2]
    exact (hok' v h1 h2).2.1
  have hlab1 : ∀ v, 0 < v → v < 2 ^ 22 → lookLB LB (vm32 22 M1 v) = lookLB LB v := fun v h1 h2 => by
    rw [← m1 v h2]
    exact (hok' v h1 h2).2.2.1
  have hv0 : ∀ v, 0 < v → v < 2 ^ 22 → 0 < vm32 22 M0 v ∧ vm32 22 M0 v < 2 ^ 22 := fun v h1 h2 =>
    ⟨Nat.pos_of_ne_zero (vm32_ne f2 i02 h2 (by omega)), vm32_lt22 f0 v⟩
  have hv1 : ∀ v, 0 < v → v < 2 ^ 22 → 0 < vm32 22 M1 v ∧ vm32 22 M1 v < 2 ^ 22 := fun v h1 h2 =>
    ⟨Nat.pos_of_ne_zero (vm32_ne f3 i13 h2 (by omega)), vm32_lt22 f1 v⟩
  have hv2 : ∀ v, 0 < v → v < 2 ^ 22 → 0 < vm32 22 M2 v ∧ vm32 22 M2 v < 2 ^ 22 := fun v h1 h2 =>
    ⟨Nat.pos_of_ne_zero (vm32_ne f0 i20 h2 (by omega)), vm32_lt22 f2 v⟩
  have hv3 : ∀ v, 0 < v → v < 2 ^ 22 → 0 < vm32 22 M3 v ∧ vm32 22 M3 v < 2 ^ 22 := fun v h1 h2 =>
    ⟨Nat.pos_of_ne_zero (vm32_ne f1 i31 h2 (by omega)), vm32_lt22 f3 v⟩
  have act0 : ∀ v, actPair M0 M1 0 v = vm32 22 M0 v := fun v => by rw [actPair, ite_eq_left rfl]
  have act1 : ∀ v, actPair M0 M1 1 v = vm32 22 M1 v := fun v => by
    rw [actPair, ite_eq_right Nat.one_ne_zero]
  have hreach : ∀ D p, Nat.shiftRight (lookDT DT p) 2 = D → 0 < p → p < 2 ^ 22 → lookLB LB p = a →
      Reach (actPair M0 M1) 2 censusValid22 (nthN reps (a - 1)) p := by
    intro D
    induction D using Nat.strong_induction_on with
    | _ D ih =>
      intro p hD h1 h2 hl
      obtain ⟨-, -, -, hz, hs⟩ := hok' p h1 h2
      by_cases hD0 : D = 0
      · have e := hz (by rw [hD, hD0])
        rw [hl] at e
        rw [e]
        exact .root
      · have hdep := hs (by rw [hD]; exact hD0)
        have hpv : censusValid22 p = true := (hvalid p).2 ⟨h1, h2⟩
        have ht : Nat.land (lookDT DT p) 3 < 4 := Nat.and_lt_two_pow (n := 2) _ (by decide)
        rcases (by omega : Nat.land (lookDT DT p) 3 = 0 ∨ Nat.land (lookDT DT p) 3 = 1 ∨
            Nat.land (lookDT DT p) 3 = 2 ∨ Nat.land (lookDT DT p) 3 = 3) with e | e | e | e <;>
          rw [e] at hdep
        ·
          have hx : Nat.xor 0 2 = 2 := rfl
          rw [hx, m2 p h2] at hdep
          obtain ⟨u1, u2⟩ := hv2 p h1 h2
          have hup : vm32 22 M0 (vm32 22 M2 p) = p := vm32_inv f0 i20 h2
          have hlu : lookLB LB (vm32 22 M2 p) = a := by
            rw [← hlab0 _ u1 u2, hup, hl]
          have hu := ih _ (by omega) _ rfl u1 u2 hlu
          exact .step 0 (by decide) ((hvalid _).2 ⟨u1, u2⟩) hpv hu (Or.inl (by rw [act0, hup]))
        · have hx : Nat.xor 1 2 = 3 := rfl
          rw [hx, m3 p h2] at hdep
          obtain ⟨u1, u2⟩ := hv3 p h1 h2
          have hup : vm32 22 M1 (vm32 22 M3 p) = p := vm32_inv f1 i31 h2
          have hlu : lookLB LB (vm32 22 M3 p) = a := by
            rw [← hlab1 _ u1 u2, hup, hl]
          have hu := ih _ (by omega) _ rfl u1 u2 hlu
          exact .step 1 (by decide) ((hvalid _).2 ⟨u1, u2⟩) hpv hu (Or.inl (by rw [act1, hup]))
        · have hx : Nat.xor 2 2 = 0 := rfl
          rw [hx, m0 p h2] at hdep
          obtain ⟨u1, u2⟩ := hv0 p h1 h2
          have hlu : lookLB LB (vm32 22 M0 p) = a := by rw [hlab0 p h1 h2, hl]
          have hu := ih _ (by omega) _ rfl u1 u2 hlu
          exact .step 0 (by decide) ((hvalid _).2 ⟨u1, u2⟩) hpv hu (Or.inr (by rw [act0]))
        · have hx : Nat.xor 3 2 = 1 := rfl
          rw [hx, m1 p h2] at hdep
          obtain ⟨u1, u2⟩ := hv1 p h1 h2
          have hlu : lookLB LB (vm32 22 M1 p) = a := by rw [hlab1 p h1 h2, hl]
          have hu := ih _ (by omega) _ rfl u1 u2 hlu
          exact .step 1 (by decide) ((hvalid _).2 ⟨u1, u2⟩) hpv hu (Or.inr (by rw [act1]))
  refine ⟨pts, ?_, ?_, ?_, fun p hp => ?_, fun p hp k hk => ?_, fun p hp => ?_⟩
  · rw [hsum, Nat.sub_zero]
    symm
    exact field_count (L := lookLB LB) (a - 1) _ (by simp)
  · exact (List.nodup_range' (s := 0) (n := 4194304)).filter _
  · rw [hmem]
    have := (hvalid (nthN reps (a - 1))).1 hrep.1
    exact ⟨this.1, this.2, Nat.eq_of_beq_eq_true hrep.2⟩
  · obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp
    exact ⟨(hvalid p).2 ⟨h1, h2⟩, h3⟩
  · obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · rw [act0, hmem]
      exact ⟨(hv0 p h1 h2).1, (hv0 p h1 h2).2, by rw [hlab0 p h1 h2, h3]⟩
    · rw [act1, hmem]
      exact ⟨(hv1 p h1 h2).1, (hv1 p h1 h2).2, by rw [hlab1 p h1 h2, h3]⟩
  · obtain ⟨h1, h2, h3⟩ := (hmem p).1 hp
    exact hreach _ p rfl h1 h2 h3

@[expose] noncomputable def sumL (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.add x ih) L

@[expose] noncomputable def noLabelBelow (LB : List (List Nat)) (a m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun n ih => andB ih (notB (Nat.beq (lookLB LB n) a))) m

@[expose] noncomputable def censusRecOK (LB : List (List Nat)) (reps cs : List Nat)
    (a root size : Nat) : Bool :=
  andB (Nat.ble (nat_lit 1) a) (andB (Nat.ble a (lenL reps))
    (andB (Nat.beq (nthN reps (Nat.sub a (nat_lit 1))) root)
      (andB (Nat.beq (Nat.mod (Nat.div (sumL cs)
          (Nat.pow (nat_lit 2) (Nat.mul (nat_lit 24) (Nat.sub a (nat_lit 1)))))
          (Nat.pow (nat_lit 2) (nat_lit 24))) size)
        (noLabelBelow LB a root))))

theorem andB_eq_true {b c : Bool} (h : andB b c = true) : b = true ∧ c = true := by
  cases b
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem sumL_eq (L : List Nat) : sumL L = L.sum := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.sum_cons, ← ih]
    rfl

theorem noLabelBelow_sound {LB : List (List Nat)} {a : Nat} :
    ∀ {m : Nat}, noLabelBelow LB a m = true → ∀ n < m, lookLB LB n ≠ a
  | 0, _, n, hn => absurd hn (Nat.not_lt_zero n)
  | m + 1, h, n, hn => by
    have e : noLabelBelow LB a (m + 1) =
        andB (noLabelBelow LB a m) (notB (Nat.beq (lookLB LB m) a)) := rfl
    obtain ⟨h1, h2⟩ := andB_eq_true (e ▸ h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hn | rfl
    · exact noLabelBelow_sound h1 n hn
    · intro he
      rw [he, Nat.beq_refl] at h2
      exact Bool.false_ne_true h2

theorem censusRecOK_sound {LB : List (List Nat)} {reps cs : List Nat} {a root size : Nat}
    (h : censusRecOK LB reps cs a root size = true) :
    1 ≤ a ∧ a ≤ lenL reps ∧ nthN reps (a - 1) = root ∧
      cs.sum / 2 ^ (24 * (a - 1)) % 2 ^ 24 = size ∧ ∀ n < root, lookLB LB n ≠ a := by
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h5⟩ := andB_eq_true h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3, ?_,
    noLabelBelow_sound h5⟩
  have e := Nat.eq_of_beq_eq_true h4
  rw [sumL_eq] at e
  exact e

end CFSG.KC.BM

end
