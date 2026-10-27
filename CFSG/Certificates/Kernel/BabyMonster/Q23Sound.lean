module

public import CFSG.Certificates.Kernel.BabyMonster.Native.Q23
public import CFSG.Certificates.Kernel.BabyMonster.Native.Census
public import CFSG.Certificates.Kernel.BabyMonster.StripLib
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.KC.BM

@[expose] noncomputable def mat32 (M : Nat) : Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  Matrix.of fun i j => if (fld32 M i).testBit j then 1 else 0

@[expose] def bz2 (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bz2_xor (a b : Bool) : bz2 (a ^^ b) = bz2 a + bz2 b := by
  cases a <;> cases b <;> decide

theorem bz2_and (a b : Bool) : bz2 (a && b) = bz2 a * bz2 b := by
  cases a <;> cases b <;> decide

theorem forceB_q (v : Nat) (k : Nat → Nat) : forceB v k = k v := by
  unfold forceB
  cases Nat.beq v 0 <;> rfl

theorem testBit_low32 (x j : Nat) (hj : j < 32) :
    (Nat.land x (nat_lit 4294967295)).testBit j = x.testBit j := by
  change (x &&& (2 ^ 32 - 1)).testBit j = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]

@[expose] noncomputable def vmLoop (k M v acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih M v acc => forceB
      (Nat.xor acc (Nat.mul (Nat.land v (nat_lit 1)) (Nat.land M (nat_lit 4294967295))))
      (fun acc' => ih (Nat.shiftRight M (nat_lit 32)) (Nat.shiftRight v (nat_lit 1)) acc'))
    k M v acc

theorem vmLoop_bit : ∀ (k M v acc : Nat) {j : Nat}, j < 32 →
    bz2 ((vmLoop k M v acc).testBit j) = bz2 (acc.testBit j) +
      ∑ l ∈ Finset.range k, bz2 (v.testBit l) * bz2 ((M >>> (32 * l)).testBit j)
  | 0, M, v, acc, j, hj => by simp [vmLoop]
  | k + 1, M, v, acc, j, hj => by
    have e : vmLoop (k + 1) M v acc = vmLoop k (M >>> 32) (v >>> 1)
        (Nat.xor acc (Nat.mul (Nat.land v 1) (Nat.land M 4294967295))) := by
      change forceB _ _ = _
      rw [forceB_q]
      rfl
    rw [e, vmLoop_bit k _ _ _ hj, Finset.sum_range_succ']
    have h1 : (Nat.xor acc (Nat.mul (Nat.land v 1) (Nat.land M 4294967295))).testBit j =
        (acc.testBit j ^^ (v.testBit 0 && M.testBit j)) := by
      change (acc ^^^ (v &&& 1) * Nat.land M (nat_lit 4294967295)).testBit j = _
      rw [Nat.testBit_xor]
      congr 1
      rcases Nat.mod_two_eq_zero_or_one v with h | h
      · have : v &&& 1 = 0 := by rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]; simpa using h
        rw [this, Nat.zero_mul, Nat.zero_testBit, Nat.testBit_zero, decide_eq_false (by omega),
          Bool.false_and]
      · have : v &&& 1 = 1 := by rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]; simpa using h
        rw [this, Nat.one_mul, testBit_low32 _ _ hj, Nat.testBit_zero, decide_eq_true h,
          Bool.true_and]
    have hs : ∀ l, (v >>> 1).testBit l = v.testBit (l + 1) := fun l => by
      rw [Nat.testBit_shiftRight, Nat.add_comm]
    have hm : ∀ l, ((M >>> 32) >>> (32 * l)).testBit j = (M >>> (32 * (l + 1))).testBit j :=
      fun l => by
        rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
        congr 1
        ring
    rw [h1, bz2_xor, bz2_and]
    simp only [hs, hm, Nat.mul_zero, Nat.shiftRight_zero]
    ring

theorem vmLoop_lt : ∀ (k M v acc : Nat), acc < 2 ^ 32 → vmLoop k M v acc < 2 ^ 32
  | 0, _, _, _, h => h
  | k + 1, M, v, acc, h => by
    have e : vmLoop (k + 1) M v acc = vmLoop k (M >>> 32) (v >>> 1)
        (Nat.xor acc (Nat.mul (Nat.land v 1) (Nat.land M 4294967295))) := by
      change forceB _ _ = _
      rw [forceB_q]
      rfl
    rw [e]
    apply vmLoop_lt
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    change (acc ^^^ (v &&& 1) * Nat.land M (nat_lit 4294967295)).testBit i = false
    rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right
      (by decide) hi))]
    have hm : (v &&& 1) * Nat.land M (nat_lit 4294967295) < 2 ^ 32 := by
      have h1 : v &&& 1 ≤ 1 := Nat.and_le_right
      have h2 : Nat.land M (nat_lit 4294967295) < 2 ^ 32 := by
        change M &&& (2 ^ 32 - 1) < _
        rw [Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (by decide)
      calc (v &&& 1) * Nat.land M (nat_lit 4294967295) ≤ 1 * Nat.land M (nat_lit 4294967295) :=
            Nat.mul_le_mul_right _ h1
        _ < 2 ^ 32 := by rw [Nat.one_mul]; exact h2
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hi))]
    rfl

@[expose] noncomputable def mmLoop (k0 B k A sh acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih A sh acc => forceB
      (Nat.lor acc (Nat.shiftLeft (vm32 k0 B (Nat.land A (nat_lit 4294967295))) sh))
      (fun acc' => ih (Nat.shiftRight A (nat_lit 32)) (Nat.add sh (nat_lit 32)) acc'))
    k A sh acc

theorem testBit_fld32 (T b j : Nat) (hj : j < 32) :
    (fld32 T b).testBit j = T.testBit (32 * b + j) := by
  unfold fld32
  rw [testBit_low32 _ _ hj]
  change (T >>> (32 * b)).testBit j = _
  rw [Nat.testBit_shiftRight, Nat.add_comm]

theorem mmLoop_bit (k0 B : Nat) : ∀ (k A s acc : Nat), acc < 2 ^ (32 * s) → ∀ i j, j < 32 →
    (mmLoop k0 B k A (32 * s) acc).testBit (32 * i + j) =
      if i < s then acc.testBit (32 * i + j)
      else if i < s + k then (vm32 k0 B (fld32 A (i - s))).testBit j else false
  | 0, A, s, acc, hacc, i, j, hj => by
    change acc.testBit (32 * i + j) = _
    split
    · rfl
    · rw [ite_eq_right (by omega)]
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide)
        (by omega)))
  | k + 1, A, s, acc, hacc, i, j, hj => by
    have hv : vm32 k0 B (Nat.land A (nat_lit 4294967295)) < 2 ^ 32 :=
      vmLoop_lt _ _ _ _ (by decide)
    set acc' := Nat.lor acc (Nat.shiftLeft (vm32 k0 B (Nat.land A (nat_lit 4294967295)))
      (32 * s)) with hacc'
    have hlt : acc' < 2 ^ (32 * (s + 1)) := by
      apply Nat.lt_pow_two_of_testBit
      intro q hq
      change (acc ||| (vm32 k0 B (Nat.land A (nat_lit 4294967295)) <<< (32 * s))).testBit q = false
      rw [Nat.testBit_or, Nat.testBit_lt_two_pow (lt_of_lt_of_le hacc
        (Nat.pow_le_pow_right (by decide) (by omega))), Nat.testBit_shiftLeft, Bool.false_or]
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide)
        (by omega))), Bool.and_false]
    have e : mmLoop k0 B (k + 1) A (32 * s) acc = mmLoop k0 B k (A >>> 32) (32 * (s + 1)) acc' := by
      change forceB _ _ = _
      rw [forceB_q]
      rfl
    rw [e, mmLoop_bit k0 B k _ (s + 1) acc' hlt i j hj]
    have hb : acc'.testBit (32 * i + j) = if i < s then acc.testBit (32 * i + j)
        else if i = s then (vm32 k0 B (fld32 A 0)).testBit j else false := by
      change (acc ||| (vm32 k0 B (Nat.land A (nat_lit 4294967295)) <<< (32 * s))).testBit
        (32 * i + j) = _
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      have hf : fld32 A 0 = Nat.land A (nat_lit 4294967295) := rfl
      rw [← hf]
      split
      · rw [decide_eq_false (by omega), Bool.false_and, Bool.or_false]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide)
          (by omega))), Bool.false_or]
        split
        · rename_i h
          subst h
          rw [decide_eq_true (by omega), Bool.true_and, show 32 * i + j - 32 * i = j by omega]
        · rw [decide_eq_true (by omega), Bool.true_and]
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide)
            (by omega)))
    have hA : ∀ i', fld32 (A >>> 32) i' = fld32 A (i' + 1) := fun i' => by
      unfold fld32
      change ((A >>> 32) >>> (32 * i')) &&& _ = (A >>> (32 * (i' + 1))) &&& _
      rw [← Nat.shiftRight_add]
      congr 2
      ring
    by_cases h1 : i < s + 1
    · rw [ite_eq_left h1, hb]
      by_cases h2 : i < s
      · rw [ite_eq_left h2, ite_eq_left h2]
      · rw [ite_eq_right h2, ite_eq_right h2, ite_eq_left (show i = s by omega),
          ite_eq_left (show i < s + (k + 1) by omega), show i - s = 0 by omega]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ i < s by omega)]
      by_cases h2 : i < s + 1 + k
      · rw [ite_eq_left h2, ite_eq_left (show i < s + (k + 1) by omega), hA,
          show i - (s + 1) + 1 = i - s by omega]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < s + (k + 1) by omega)]

theorem mm32_bit (A B : Nat) {i j : Nat} (hi : i < 22) (hj : j < 32) :
    (fld32 (mm32 22 A B) i).testBit j = (vm32 22 B (fld32 A i)).testBit j := by
  rw [testBit_fld32 _ _ _ hj]
  have h := mmLoop_bit 22 B 22 A 0 0 (by decide) i j hj
  rw [Nat.mul_zero] at h
  have e : mm32 22 A B = mmLoop 22 B 22 A 0 0 := rfl
  rw [e, h, ite_eq_right (show ¬ i < 0 by omega), ite_eq_left (show i < 0 + 22 by omega),
    Nat.sub_zero]

theorem mm32_mat (A B : Nat) : mat32 (mm32 22 A B) = mat32 A * mat32 B := by
  ext i j
  have hj : j.val < 32 := by omega
  have lhs : mat32 (mm32 22 A B) i j = bz2 ((vm32 22 B (fld32 A i)).testBit j) := by
    change bz2 ((fld32 (mm32 22 A B) i).testBit j) = _
    rw [mm32_bit A B i.2 hj]
  have e : vm32 22 B (fld32 A i) = vmLoop 22 B (fld32 A i) 0 := rfl
  have hent : ∀ l : Fin 22, mat32 A i l * mat32 B l j =
      bz2 ((fld32 A i).testBit l) * bz2 ((B >>> (32 * l.val)).testBit j) := by
    intro l
    change bz2 _ * bz2 ((fld32 B l).testBit j) = _
    rw [testBit_fld32 _ _ _ hj, Nat.testBit_shiftRight, Nat.add_comm]
  rw [Matrix.mul_apply, lhs, e, vmLoop_bit _ _ _ _ hj, Nat.zero_testBit,
    show bz2 false = 0 from rfl, zero_add, Finset.sum_range]
  exact Finset.sum_congr rfl fun l _ => (hent l).symm

@[expose] noncomputable def eBody (fromK : Bool) (k i r st : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) st (echStep r st) (Nat.ble k i))
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) st (Nat.beq r (nat_lit 0)))
      (echStep r st) (Nat.blt i k))
    (notB fromK)

@[expose] noncomputable def eLoop (fromK : Bool) (k n R i st : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ st => st)
    (fun _ ih R i st => forceB (eBody fromK k i (Nat.land R (nat_lit 4294967295)) st)
      (fun st' => ih (Nat.shiftRight R (nat_lit 32)) (Nat.succ i) st')) n R i st

theorem fld32_shr (R l : Nat) : fld32 (R >>> 32) l = fld32 R (l + 1) := by
  unfold fld32
  change ((R >>> 32) >>> (32 * l)) &&& _ = (R >>> (32 * (l + 1))) &&& _
  rw [← Nat.shiftRight_add]
  congr 2
  omega

theorem eLoop_eq (fromK : Bool) (k : Nat) : ∀ (n R i st : Nat),
    eLoop fromK k n R i st =
      (List.range n).foldl (fun st l => eBody fromK k (i + l) (fld32 R l) st) st
  | 0, _, _, _ => rfl
  | n + 1, R, i, st => by
    have e : eLoop fromK k (n + 1) R i st =
        eLoop fromK k n (R >>> 32) (i + 1) (eBody fromK k i (fld32 R 0) st) := by
      change forceB _ _ = _
      rw [forceB_q]
      rfl
    rw [e, eLoop_eq fromK k n]
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, Nat.add_zero]
    congr 1
    funext st' l
    have e2 : i + 1 + l = i + (l + 1) := by omega
    rw [fld32_shr, e2]

theorem ech22_fold {fromK : Bool} {Q k : Nat} (h : ech22 fromK Q k = true) :
    (List.range 22).foldl (fun st i => eBody fromK k i (fld32 Q i) st)
      (Nat.shiftLeft 1 40) ≠ 0 := by
  have e : ech22 fromK Q k = Nat.blt 0 (eLoop fromK k 22 Q 0 (Nat.shiftLeft 1 40)) := rfl
  rw [e, eLoop_eq, Nat.blt_eq] at h
  simp only [Nat.zero_add] at h
  omega

theorem fld32_lt (T b : Nat) : fld32 T b < 2 ^ 32 := by
  unfold fld32
  change (T >>> (32 * b)) &&& (2 ^ 32 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by decide)

theorem wfRec (M : Nat) : ∀ n, Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB ih (Nat.beq (Nat.shiftRight (fld32 M i) (nat_lit 22)) (nat_lit 0))) n =
        true → ∀ i < n, fld32 M i < 2 ^ 22
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    change andB _ _ = true at h
    rw [CFSG.KC.BM.SL.andB_eq, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · exact wfRec M n h.1 i hi
    · subst hi
      have h2 := Nat.eq_of_beq_eq_true h.2
      rw [CFSG.KC.BM.SL.nshr, Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 (by norm_num)
      · exact h2

theorem wf_fields {M : Nat} (h : wf32 22 M = true) : ∀ i < 22, fld32 M i < 2 ^ 22 := by
  change andB _ (Nat.rec (motive := fun _ => Bool) true
      (fun i ih => andB ih (Nat.beq (Nat.shiftRight (fld32 M i) (nat_lit 22)) (nat_lit 0))) 22)
    = true at h
  rw [CFSG.KC.BM.SL.andB_eq, Bool.and_eq_true] at h
  exact wfRec M 22 h.2

theorem vm32_lt22 {M : Nat} (hM : ∀ l < 22, fld32 M l < 2 ^ 22) (v : Nat) :
    vm32 22 M v < 2 ^ 22 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  change (vmLoop 22 M v 0).testBit j = false
  by_cases hj32 : j < 32
  · have e := vmLoop_bit 22 M v 0 hj32
    have hs : ∑ l ∈ Finset.range 22, bz2 (v.testBit l) * bz2 ((M >>> (32 * l)).testBit j) =
        0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [Finset.mem_range] at hl
      have hb : (M >>> (32 * l)).testBit j = false := by
        rw [Nat.testBit_shiftRight, ← testBit_fld32 M l j hj32]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (hM l hl)
          (Nat.pow_le_pow_right (by norm_num) hj))
      rw [hb]
      simp [bz2]
    rw [hs, Nat.zero_testBit, add_zero] at e
    cases hc : (vmLoop 22 M v 0).testBit j
    · rfl
    · rw [hc] at e
      exact absurd e (by decide)
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (vmLoop_lt 22 M v 0 (by decide))
      (Nat.pow_le_pow_right (by norm_num) (by omega)))

theorem fld_mm (P M : Nat) {i : Nat} (hi : i < 22) :
    fld32 (mm32 22 P M) i = vm32 22 M (fld32 P i) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 32
  · exact mm32_bit P M hi hj
  · have hv : vm32 22 M (fld32 P i) < 2 ^ 32 := vmLoop_lt 22 M _ 0 (by decide)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (fld32_lt _ _)
        (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem linIndep_rows22 {ι : Type*} (r : ι → Nat) (hne : ∀ i, r i ≠ 0) (hlt : ∀ i, r i < 2 ^ 22)
    (hinj : ∀ i i', (r i).log2 = (r i').log2 → i = i') :
    LinearIndependent (ZMod 2)
      (fun i (j : Fin 22) => if (r i).testBit j then (1 : ZMod 2) else 0) := by
  have hlog : ∀ i, (r i).log2 < 22 := fun i => (Nat.log2_lt (hne i)).2 (hlt i)
  apply CFSG.KC.BM.SL.linIndep_of_lead _ (fun i => ⟨(r i).log2, hlog i⟩)
  · intro i
    simp [Nat.testBit_log2 (hne i)]
  · intro i j hij
    have hij' : (r i).log2 < j.val := hij
    have hb : (r i).testBit j.val = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (@Nat.lt_log2_self _)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hb]
  · intro i i' e
    exact hinj i i' (congrArg Fin.val e)

theorem log2_inj_of {row : Nat → Nat} {act : Nat → Bool} {p : Fin 22 → Prop}
    (hp : ∀ i, p i → act i.val = true)
    (C : ∀ i i', i < i' → i' < 22 → act i = true → act i' = true → (row i').log2 < (row i).log2)
    (i i' : {i : Fin 22 // p i}) (e : (row i.val.val).log2 = (row i'.val.val).log2) : i = i' := by
  by_contra hne
  have hne' : i.val.val ≠ i'.val.val := fun e' => hne (Subtype.ext (Fin.ext e'))
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
  · have := C _ _ hlt i'.val.isLt (hp _ i.property) (hp _ i'.property)
    omega
  · have := C _ _ hlt i.val.isLt (hp _ i'.property) (hp _ i.property)
    omega

theorem rank22_sound {M P Q k : Nat} (hk : k ≤ 22) (hM : wf32 22 M = true)
    (h : rank22 M P Q k = true) : (mat32 M).rank = k := by
  unfold rank22 at h
  rw [CFSG.KC.BM.SL.andB_eq, CFSG.KC.BM.SL.andB_eq, CFSG.KC.BM.SL.andB_eq, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hP, hQ⟩, hEQ, hEP⟩ := h
  have hQ' := Nat.eq_of_beq_eq_true hQ
  have hPf := wf_fields hP
  have hQf : ∀ i < 22, fld32 Q i < 2 ^ 22 := by
    intro i hi
    rw [← hQ', fld_mm P M hi]
    exact vm32_lt22 (wf_fields hM) _
  have hmat : mat32 Q = mat32 P * mat32 M := by rw [← hQ', mm32_mat]
  have hfQ : (List.range 22).foldl (fun st i => if Nat.blt i k then echStep (fld32 Q i) st
      else if Nat.beq (fld32 Q i) 0 then st else 0) (Nat.shiftLeft 1 40) ≠ 0 := by
    have hf : (fun st i => eBody false k i (fld32 Q i) st) = (fun st i => if Nat.blt i k then
        echStep (fld32 Q i) st else if Nat.beq (fld32 Q i) 0 then st else 0) := by
      funext st i
      unfold eBody
      cases Nat.blt i k <;> cases Nat.beq (fld32 Q i) 0 <;> rfl
    have := ech22_fold hEQ
    rw [hf] at this
    exact this
  have hfP : (List.range 22).foldl (fun st i => if Nat.ble k i then echStep (fld32 P i) st
      else if true then st else 0) (Nat.shiftLeft 1 40) ≠ 0 := by
    have hf : (fun st i => eBody true k i (fld32 P i) st) = (fun st i => if Nat.ble k i then
        echStep (fld32 P i) st else if true then st else 0) := by
      funext st i
      unfold eBody
      cases Nat.ble k i <;> rfl
    have := ech22_fold hEP
    rw [hf] at this
    exact this
  obtain ⟨A1, B1, C1, -⟩ := CFSG.KC.BM.SL.ech_fold (fun i => Nat.blt i k) (fun _ r => Nat.beq r 0)
    (fld32 Q) (Nat.shiftLeft 1 40) 22 hfQ
  obtain ⟨A2, -, C2, -⟩ := CFSG.KC.BM.SL.ech_fold (fun i => Nat.ble k i) (fun _ _ => true)
    (fld32 P) (Nat.shiftLeft 1 40) 22 hfP
  have hp1 : ∀ i : Fin 22, i.val < k → Nat.blt i.val k = true := fun i hi => by
    rw [Nat.blt_eq]
    exact hi
  have hp2 : ∀ i : Fin 22, ¬ i.val < k → Nat.ble k i.val = true := fun i hi => by
    rw [Nat.ble_eq]
    omega
  have hli1 : LinearIndependent (ZMod 2)
      ((mat32 Q).submatrix (fun i : {i : Fin 22 // i.val < k} => i.val) id).row :=
    linIndep_rows22 (fun i : {i : Fin 22 // i.val < k} => fld32 Q i.val)
      (fun i => A1 _ i.val.isLt (hp1 _ i.property)) (fun i => hQf _ i.val.isLt)
      (log2_inj_of hp1 C1)
  have hli2 : LinearIndependent (ZMod 2)
      ((mat32 P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id).row :=
    linIndep_rows22 (fun i : {i : Fin 22 // ¬ i.val < k} => fld32 P i.val)
      (fun i => A2 _ i.val.isLt (hp2 _ i.property)) (fun i => hPf _ i.val.isLt)
      (log2_inj_of hp2 C2)
  have hz : (mat32 P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id * mat32 M =
      0 := by
    ext i j
    have e1 : ((mat32 P).submatrix (fun i : {i : Fin 22 // ¬ i.val < k} => i.val) id *
        mat32 M) i j = (mat32 P * mat32 M) i.val j := by
      simp [Matrix.mul_apply]
    have hb := B1 i.val.val i.val.isLt (by
      rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
      exact i.property)
    have h0 : fld32 Q i.val.val = 0 := Nat.eq_of_beq_eq_true hb
    rw [e1, ← hmat, Matrix.zero_apply]
    simp [mat32, h0]
  have hlo : k ≤ (mat32 M).rank := by
    have h1 := LinearIndependent.rank_matrix hli1
    rw [Fintype.card_fin_lt_of_le hk] at h1
    calc k = _ := h1.symm
      _ ≤ (mat32 Q).rank := Matrix.rank_submatrix_le _ _ _
      _ ≤ (mat32 M).rank := by
        rw [hmat]
        exact Matrix.rank_mul_le_right _ _
  have hhi := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz
  rw [LinearIndependent.rank_matrix hli2, Fintype.card_subtype_compl,
    Fintype.card_fin_lt_of_le hk, Fintype.card_fin] at hhi
  omega

theorem id32_bits : ∀ i < 22, ∀ j < 22, (fld32 (id32 22) i).testBit j = decide (i = j) := by
  decide +kernel

theorem id32_mat : mat32 (id32 22) = 1 := by
  ext i j
  rw [mat32, Matrix.of_apply, id32_bits i i.2 j j.2, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    simp [h, h']

end CFSG.KC.BM

end
