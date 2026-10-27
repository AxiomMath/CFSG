module

public import CFSG.Certificates.Kernel.Common.DceS
import Mathlib.Tactic.IntervalCases
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.P16

open CFSG.KC CFSG.KC.DceS CFSG.KC.Loop

@[expose] noncomputable def fl (x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul 4 i)) 15

theorem fl_lt (x i : Nat) : fl x i < 16 :=
  Nat.and_lt_two_pow (Nat.shiftRight x (Nat.mul 4 i)) (y := 15) (n := 4) (by norm_num)

theorem testBit_fl (x i k : Nat) : (fl x i).testBit k = (decide (k < 4) && x.testBit (4 * i + k)) := by
  unfold fl
  rw [Nat.land_eq, Nat.shiftRight_eq', Nat.testBit_and, Nat.testBit_shiftRight]
  have e : (15 : Nat) = 2 ^ 4 - 1 := rfl
  rw [e, Nat.testBit_two_pow_sub_one, Bool.and_comm]
  rfl

theorem eq_of_fl {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : ∀ i < 16, fl a i = fl b i) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 64
  · have e : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
    have hk : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h1 := testBit_fl a (n / 4) (n % 4)
    have h2 := testBit_fl b (n / 4) (n % 4)
    rw [← e] at h1 h2
    simp only [hk, decide_true, Bool.true_and] at h1 h2
    rw [← h1, ← h2, h (n / 4) (by omega)]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem shr60 {a : Nat} (ha : a < 2 ^ 64) : Nat.shiftRight a (nat_lit 60) = fl a 15 := by
  have h : a >>> 60 < 2 ^ 4 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by simpa using ha)
  have e : fl a 15 = (a >>> 60) &&& (2 ^ 4 - 1) := rfl
  rw [e, Nat.and_two_pow_sub_one_of_lt_two_pow h]
  rfl

private theorem pmul_bit (a b m k : Nat) (ha : a < 2 ^ 64) (hm : m < 16) (hk : k < 4) :
    (pmul a b).testBit (4 * m + k) = b.testBit (4 * fl a m + k) := by
  unfold pmul
  rw [shr60 ha]
  have e : ∀ x : Nat, Nat.shiftLeft x 2 = 4 * x := fun x => by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    ring
  have hf : ∀ i, Nat.land (Nat.shiftRight a (Nat.mul 4 i)) 15 = fl a i := fun _ => rfl
  have h1 : Nat.land a 15 = fl a 0 := by
    unfold fl
    rfl
  have h2 : ∀ i, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) → Nat.land (Nat.shiftRight a (4 * i)) 15 = fl a i :=
    fun _ _ => rfl
  rw [h1, h2 1 (by omega), h2 2 (by omega), h2 3 (by omega), h2 4 (by omega), h2 5 (by omega),
    h2 6 (by omega), h2 7 (by omega), h2 8 (by omega), h2 9 (by omega), h2 10 (by omega),
    h2 11 (by omega), h2 12 (by omega), h2 13 (by omega), h2 14 (by omega)]
  simp only [e, Nat.lor_eq, Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq']
  have t15 : ∀ j, j < 4 → Nat.testBit 15 j = true := fun j hj => by
    interval_cases j <;> rfl
  have t15' : ∀ j, 4 ≤ j → Nat.testBit 15 j = false := fun j hj =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj))
  interval_cases m <;> interval_cases k <;>
    simp [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight, t15, t15']

theorem fl_pmul {a b : Nat} (ha : a < 2 ^ 64) {m : Nat} (hm : m < 16) :
    fl (pmul a b) m = fl b (fl a m) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_fl, testBit_fl]
  by_cases hk : k < 4
  · simp only [hk, decide_true, Bool.true_and]
    exact pmul_bit a b m k ha hm hk
  · simp [hk]

private theorem lt_term (x s : Nat) (hs : s ≤ 60) : (x &&& 15) <<< s < 2 ^ 64 := by
  rw [Nat.shiftLeft_eq]
  have h1 : x &&& 15 < 2 ^ 4 := Nat.and_lt_two_pow x (by norm_num)
  have h2 : 2 ^ s ≤ 2 ^ 60 := Nat.pow_le_pow_right (by norm_num) hs
  calc (x &&& 15) * 2 ^ s < 2 ^ 4 * 2 ^ s := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos s)
    _ ≤ 2 ^ 4 * 2 ^ 60 := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 64 := by norm_num

private theorem or16_lt {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Nat}
    (h0 : x0 < 2 ^ 64) (h1 : x1 < 2 ^ 64) (h2 : x2 < 2 ^ 64) (h3 : x3 < 2 ^ 64)
    (h4 : x4 < 2 ^ 64) (h5 : x5 < 2 ^ 64) (h6 : x6 < 2 ^ 64) (h7 : x7 < 2 ^ 64)
    (h8 : x8 < 2 ^ 64) (h9 : x9 < 2 ^ 64) (h10 : x10 < 2 ^ 64) (h11 : x11 < 2 ^ 64)
    (h12 : x12 < 2 ^ 64) (h13 : x13 < 2 ^ 64) (h14 : x14 < 2 ^ 64) (h15 : x15 < 2 ^ 64) :
    x0 ||| (x1 ||| (x2 ||| (x3 ||| (x4 ||| (x5 ||| (x6 ||| (x7 ||| (x8 ||| (x9 ||| (x10 |||
      (x11 ||| (x12 ||| (x13 ||| (x14 ||| x15)))))))))))))) < 2 ^ 64 := by
  repeat (first | assumption | apply Nat.or_lt_two_pow)

theorem pmul_lt (a b : Nat) : pmul a b < 2 ^ 64 := by
  unfold pmul
  simp only [Nat.lor_eq, Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftRight_eq']
  exact or16_lt (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ (n := 4) (by norm_num)) (by norm_num))
    (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num))
    (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num))
    (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num))
    (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num))
    (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num)) (lt_term _ _ (by norm_num))

private theorem term_bit (i f fm k : Nat) (hi : i < 16) (hk : k < 4) :
    (i <<< (4 * f)).testBit (4 * fm + k) = (decide (f = fm) && i.testBit k) := by
  rw [Nat.testBit_shiftLeft]
  rcases Nat.lt_trichotomy f fm with h | h | h
  · have hidx : 4 ≤ 4 * fm + k - 4 * f := by omega
    have hb : i.testBit (4 * fm + k - 4 * f) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi
        (Nat.le_trans (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) hidx)))
    rw [hb]
    simp [Nat.ne_of_lt h]
  · subst h
    have e : 4 * f + k - 4 * f = k := by omega
    simp [e]
  · have h' : ¬ 4 * fm + k ≥ 4 * f := by omega
    simp [h', Nat.ne_of_gt h]

private theorem term_lt (i f : Nat) (hi : i < 16) (hf : f < 16) : i <<< (4 * f) < 2 ^ 64 := by
  rw [Nat.shiftLeft_eq]
  have h2 : 2 ^ (4 * f) ≤ 2 ^ 60 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc i * 2 ^ (4 * f) < 16 * 2 ^ (4 * f) := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos _)
    _ ≤ 16 * 2 ^ 60 := Nat.mul_le_mul_left _ h2
    _ = 2 ^ 64 := by norm_num

private theorem pinv_eq {a : Nat} (ha : a < 2 ^ 64) : pinv a =
    0 <<< (4 * fl a 0) ||| (1 <<< (4 * fl a 1) ||| (2 <<< (4 * fl a 2) ||| (3 <<< (4 * fl a 3) |||
    (4 <<< (4 * fl a 4) ||| (5 <<< (4 * fl a 5) ||| (6 <<< (4 * fl a 6) ||| (7 <<< (4 * fl a 7) |||
    (8 <<< (4 * fl a 8) ||| (9 <<< (4 * fl a 9) ||| (10 <<< (4 * fl a 10) ||| (11 <<< (4 * fl a 11) |||
    (12 <<< (4 * fl a 12) ||| (13 <<< (4 * fl a 13) ||| (14 <<< (4 * fl a 14) |||
    15 <<< (4 * fl a 15))))))))))))))) := by
  unfold pinv
  rw [shr60 ha]
  have e : ∀ x : Nat, Nat.shiftLeft x 2 = 4 * x := fun x => by
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
    ring
  have h1 : Nat.land a 15 = fl a 0 := rfl
  have h2 : ∀ i, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) → Nat.land (Nat.shiftRight a (4 * i)) 15 = fl a i :=
    fun _ _ => rfl
  rw [h1, h2 1 (by omega), h2 2 (by omega), h2 3 (by omega), h2 4 (by omega), h2 5 (by omega),
    h2 6 (by omega), h2 7 (by omega), h2 8 (by omega), h2 9 (by omega), h2 10 (by omega),
    h2 11 (by omega), h2 12 (by omega), h2 13 (by omega), h2 14 (by omega)]
  simp only [e, Nat.lor_eq, Nat.shiftLeft_eq']

theorem pinv_lt (a : Nat) (ha : a < 2 ^ 64) : pinv a < 2 ^ 64 := by
  rw [pinv_eq ha]
  exact or16_lt (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))
    (term_lt _ _ (by norm_num) (fl_lt _ _)) (term_lt _ _ (by norm_num) (fl_lt _ _))

private theorem pinv_bit {a m k : Nat} (ha : a < 2 ^ 64)
    (hinj : ∀ i < 16, ∀ j < 16, fl a i = fl a j → i = j) (hm : m < 16) (hk : k < 4) :
    (pinv a).testBit (4 * fl a m + k) = m.testBit k := by
  rw [pinv_eq ha]
  have hne : ∀ i < 16, ∀ j < 16, i ≠ j → (fl a i = fl a j) = False :=
    fun i hi j hj hij => eq_false fun h => hij (hinj i hi j hj h)
  interval_cases m <;> simp [-Nat.testBit_shiftLeft, Nat.testBit_or, term_bit, hk, hne]

@[expose] def IsP (a : Nat) : Prop := a < 2 ^ 64 ∧ ∀ v < 16, ∃ i < 16, fl a i = v

@[expose] noncomputable def flF (a : Nat) (i : Fin 16) : Fin 16 := ⟨fl a i.val, fl_lt a i.val⟩

theorem flF_bij {a : Nat} (h : IsP a) : Function.Bijective (flF a) := by
  have hs : Function.Surjective (flF a) := fun v => by
    obtain ⟨i, hi, e⟩ := h.2 v.val v.isLt
    exact ⟨⟨i, hi⟩, Fin.ext e⟩
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

theorem isP_inj {a : Nat} (h : IsP a) : ∀ i < 16, ∀ j < 16, fl a i = fl a j → i = j := by
  intro i hi j hj e
  have := (flF_bij h).1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Fin.ext e)
  exact congrArg Fin.val this

theorem isP_pos {a : Nat} (h : IsP a) : 0 < a := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · obtain ⟨i, -, e⟩ := h.2 1 (by norm_num)
    subst h0
    have : fl 0 i = 0 := by
      unfold fl
      simp
    omega
  · exact h0

open Classical in
noncomputable def perm16 (a : Nat) : Equiv.Perm (Fin 16) :=
  if h : IsP a then (Equiv.ofBijective (flF a) (flF_bij h)).symm else 1

theorem perm16_inv_apply {a : Nat} (h : IsP a) (i : Fin 16) : (perm16 a)⁻¹ i = flF a i := by
  unfold perm16
  split_ifs
  rfl

theorem perm16_inj {a b : Nat} (ha : IsP a) (hb : IsP b) (h : perm16 a = perm16 b) : a = b := by
  refine eq_of_fl ha.1 hb.1 fun i hi => ?_
  have e := congrArg (fun p : Equiv.Perm (Fin 16) => (p⁻¹ ⟨i, hi⟩ : Fin 16).val) h
  simp only [perm16_inv_apply ha, perm16_inv_apply hb, flF] at e
  exact e

theorem isP_pmul {a b : Nat} (ha : IsP a) (hb : IsP b) : IsP (pmul a b) := by
  refine ⟨pmul_lt a b, fun v hv => ?_⟩
  obtain ⟨j, hj, ej⟩ := hb.2 v hv
  obtain ⟨i, hi, ei⟩ := ha.2 j hj
  exact ⟨i, hi, by rw [fl_pmul ha.1 hi, ei, ej]⟩

theorem perm16_pmul {a b : Nat} (ha : IsP a) (hb : IsP b) :
    perm16 (pmul a b) = perm16 a * perm16 b := by
  apply inv_injective
  rw [mul_inv_rev]
  apply Equiv.ext
  intro i
  rw [perm16_inv_apply (isP_pmul ha hb), Equiv.Perm.mul_apply, perm16_inv_apply hb,
    perm16_inv_apply ha]
  apply Fin.ext
  exact fl_pmul ha.1 i.isLt

theorem fl_pinv {a : Nat} (ha : IsP a) {m : Nat} (hm : m < 16) : fl (pinv a) (fl a m) = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_fl]
  by_cases hk : k < 4
  · simp only [hk, decide_true, Bool.true_and]
    exact pinv_bit ha.1 (isP_inj ha) hm hk
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.le_trans
      (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hk))))).symm

theorem isP_pinv {a : Nat} (ha : IsP a) : IsP (pinv a) :=
  ⟨pinv_lt a ha.1, fun v hv => ⟨fl a v, fl_lt a v, fl_pinv ha hv⟩⟩

theorem perm16_pinv {a : Nat} (ha : IsP a) : perm16 (pinv a) = (perm16 a)⁻¹ := by
  have h : (perm16 (pinv a))⁻¹ * (perm16 a)⁻¹ = 1 := by
    apply Equiv.ext
    intro j
    rw [Equiv.Perm.mul_apply, perm16_inv_apply ha, perm16_inv_apply (isP_pinv ha)]
    apply Fin.ext
    exact fl_pinv ha j.isLt
  rw [mul_eq_one_iff_eq_inv, inv_inv] at h
  rw [← h, inv_inv]

theorem fl_idP {i : Nat} (hi : i < 16) : fl idP i = i := by
  interval_cases i <;> rfl

theorem isP_idP : IsP idP :=
  ⟨by unfold idP; norm_num, fun v hv => ⟨v, hv, fl_idP hv⟩⟩

theorem perm16_idP : perm16 idP = 1 := by
  apply inv_injective
  rw [inv_one]
  apply Equiv.ext
  intro i
  rw [perm16_inv_apply isP_idP]
  exact Fin.ext (fl_idP i.isLt)

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem andB_intro {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  subst ha hb
  rfl

theorem isP_of_isPerm {a : Nat} (h : isPerm a = true) : IsP a := by
  unfold isPerm at h
  obtain ⟨h1, h2⟩ := andB_true h
  have ha : a < 2 ^ 64 := Nat.lt_of_lt_of_eq (Nat.blt_eq.mp h1) (by norm_num)
  refine ⟨ha, fun v hv => ?_⟩
  by_contra hc
  have hne : ∀ i < 16, (fl a i = v) = False := fun i hi => eq_false fun e => hc ⟨i, hi, e⟩
  have hb := Nat.eq_of_beq_eq_true h2
  rw [shr60 ha] at hb
  have h1 : Nat.land a 15 = fl a 0 := rfl
  have h2 : ∀ i, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) → Nat.land (Nat.shiftRight a (4 * i)) 15 = fl a i :=
    fun _ _ => rfl
  rw [h1, h2 1 (by omega), h2 2 (by omega), h2 3 (by omega), h2 4 (by omega), h2 5 (by omega),
    h2 6 (by omega), h2 7 (by omega), h2 8 (by omega), h2 9 (by omega), h2 10 (by omega),
    h2 11 (by omega), h2 12 (by omega), h2 13 (by omega), h2 14 (by omega)] at hb
  have ht : Nat.testBit (nat_lit 65535) v = true := by
    interval_cases v <;> rfl
  rw [hb] at ht
  simp [Nat.lor_eq, Nat.shiftLeft_eq', Nat.one_shiftLeft, hne] at ht

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem letB_eq (v : Nat) (k : Nat → Bool) : letB v k = k v := by
  cases v <;> rfl

private theorem rec_and {f : Nat → Bool} : ∀ m,
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m = true →
      ∀ g < m, f g = true
  | 0, _, g, hg => absurd hg (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    have h' : andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) m)
        (f m) = true := h
    obtain ⟨h1, h2⟩ := andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact rec_and m h1 g hg
    · exact h2

@[expose] noncomputable def eCode (ET : Nat → Nat) (off i : Nat) : Nat :=
  Nat.land (eRec ET (Nat.add off i)) m64

@[expose] def Chk (ET : Nat → Nat) (G ng n off t prev : Nat) : Prop :=
  (t = 0 ∨ prev < eCode ET off t) ∧
  (eRoot (eRec ET (Nat.add off t)) = true → eCode ET off t = idP) ∧
  (eRoot (eRec ET (Nat.add off t)) = false → eP (eRec ET (Nat.add off t)) < n ∧
    eK (eRec ET (Nat.add off t)) < ng ∧
    eRank (eRec ET (Nat.add off (eP (eRec ET (Nat.add off t))))) < eRank (eRec ET (Nat.add off t)) ∧
    eCode ET off t = pmul (eCode ET off (eP (eRec ET (Nat.add off t)))) (gk G (eK (eRec ET (Nat.add off t))))) ∧
  (∀ k < ng, eC (eRec ET (Nat.add off t)) k < n ∧
    pmul (eCode ET off t) (gk G k) = eCode ET off (eC (eRec ET (Nat.add off t)) k))

private theorem brec_ne {c : Bool} {x : Nat} (h : Bool.rec (motive := fun _ => Nat) (nat_lit 0) x c ≠ 0) :
    c = true ∧ Bool.rec (motive := fun _ => Nat) (nat_lit 0) x c = x := by
  cases c
  · exact absurd rfl h
  · exact ⟨rfl, rfl⟩

private theorem eStep_spec {ET : Nat → Nat} {G ng n off S t : Nat}
    (hc : eCnt S = t + 1) (hne : eStep ET G ng n off S ≠ 0) :
    eStep ET G ng n off S = Nat.lor (t + 2) (Nat.shiftLeft (eCode ET off t) (nat_lit 24)) ∧
      Chk ET G ng n off t (ePrev S) := by
  have e : Nat.add off (Nat.sub (eCnt S) (nat_lit 1)) = Nat.add off t := by
    rw [hc]
    rfl
  unfold eStep at hne ⊢
  obtain ⟨-, hv⟩ := brec_ne hne
  rw [hv] at hne ⊢
  rw [strictN_eq', e] at hne ⊢
  obtain ⟨hcond, hval⟩ := brec_ne hne
  rw [hval, hc]
  refine ⟨rfl, ?_⟩
  obtain ⟨c1, hcond⟩ := andB_true hcond
  obtain ⟨c2, c3⟩ := andB_true hcond
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases h1 : Nat.beq (eCnt S) (nat_lit 1)
    · rw [h1] at c1
      exact Or.inr (Nat.blt_eq.mp c1)
    · left
      have h1' : eCnt S = 1 := Nat.eq_of_beq_eq_true h1
      omega
  · intro hr
    rw [hr] at c2
    exact Nat.eq_of_beq_eq_true c2
  · intro hr
    rw [hr] at c2
    obtain ⟨d1, c2⟩ := andB_true c2
    obtain ⟨d2, c2⟩ := andB_true c2
    rw [letB_eq] at c2
    obtain ⟨d3, d4⟩ := andB_true c2
    exact ⟨Nat.blt_eq.mp d1, Nat.blt_eq.mp d2, Nat.blt_eq.mp d3, Nat.eq_of_beq_eq_true d4⟩
  · intro k hk
    obtain ⟨d1, d2⟩ := andB_true (rec_and _ c3 k hk)
    exact ⟨Nat.blt_eq.mp d1, Nat.eq_of_beq_eq_true d2⟩

private theorem eStep_zero (ET : Nat → Nat) (G ng n off : Nat) : eStep ET G ng n off 0 = 0 := rfl

private theorem enumRun_iter (ET : Nat → Nat) (G ng n off : Nat) :
    ∀ m S, enumRun ET G ng n off m S = (eStep ET G ng n off)^[m] S
  | 0, _ => rfl
  | m + 1, S => by
    have e : enumRun ET G ng n off (m + 1) S = enumRun ET G ng n off m (eStep ET G ng n off S) :=
      strictN_eq' _ _
    rw [e, enumRun_iter ET G ng n off m, Function.iterate_succ_apply]

noncomputable def stAt (ET : Nat → Nat) (off : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => Nat.lor (t + 2) (Nat.shiftLeft (eCode ET off t) (nat_lit 24))

private theorem lor_eq_add {t c : Nat} (ht : t < 2 ^ 24) :
    Nat.lor t (Nat.shiftLeft c (nat_lit 24)) = c * 2 ^ 24 + t := by
  rw [Nat.lor_eq, Nat.shiftLeft_eq', Nat.or_comm]
  change c <<< 24 ||| t = c * 2 ^ 24 + t
  rw [← Nat.shiftLeft_add_eq_or_of_lt ht, Nat.shiftLeft_eq]

private theorem eCnt_eq (S : Nat) : eCnt S = S &&& (2 ^ 24 - 1) := rfl
private theorem ePrev_eq (S : Nat) : ePrev S = S >>> 24 := rfl

private theorem stAt_facts (ET : Nat → Nat) (off t : Nat) (ht : t + 1 < 2 ^ 24) :
    0 < stAt ET off t ∧ eCnt (stAt ET off t) = t + 1 ∧
      ∀ s, t = s + 1 → ePrev (stAt ET off t) = eCode ET off s := by
  cases t with
  | zero =>
    have e : stAt ET off 0 = 1 := rfl
    rw [e]
    refine ⟨Nat.one_pos, ?_, fun s hs => absurd hs (by omega)⟩
    rw [eCnt_eq, Nat.and_two_pow_sub_one_eq_mod]
  | succ s =>
    have e : stAt ET off (s + 1) = eCode ET off s * 2 ^ 24 + (s + 2) := lor_eq_add (by omega)
    rw [e]
    refine ⟨by omega, ?_, fun s' hs => ?_⟩
    · rw [eCnt_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.add_comm, Nat.add_mul_mod_self_right]
      exact Nat.mod_eq_of_lt (by omega)
    · have hs' : s' = s := by omega
      subst hs'
      rw [ePrev_eq, Nat.shiftRight_eq_div_pow, Nat.add_comm,
        Nat.add_mul_div_right _ _ (Nat.two_pow_pos 24), Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem enum_checks {ET : Nat → Nat} {G ng n off : Nat}
    (h : Nat.beq (eCnt (enumRun ET G ng n off n 1)) (Nat.succ n) = true) :
    n + 1 < 2 ^ 24 ∧ ∀ t < n, Chk ET G ng n off t (ePrev (stAt ET off t)) := by
  have hcnt := Nat.eq_of_beq_eq_true h
  have hn : n + 1 < 2 ^ 24 := by
    have hlt : eCnt (enumRun ET G ng n off n 1) < 2 ^ 24 := by
      unfold eCnt
      change _ &&& (2 ^ 24 - 1) < 2 ^ 24
      exact Nat.and_lt_two_pow _ (by norm_num)
    omega
  refine ⟨hn, ?_⟩
  let F := eStep ET G ng n off
  have key : ∀ t ≤ n, F^[t] 1 = 0 ∨
      (F^[t] 1 = stAt ET off t ∧ ∀ i < t, Chk ET G ng n off i (ePrev (stAt ET off i))) := by
    intro t
    induction t with
    | zero => exact fun _ => Or.inr ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ t ih =>
      intro htn
      rw [Function.iterate_succ_apply']
      rcases ih (by omega) with h0 | ⟨hst, hchk⟩
      · left
        rw [h0]
        exact eStep_zero ET G ng n off
      · rw [hst]
        by_cases hz : F (stAt ET off t) = 0
        · exact Or.inl hz
        · right
          obtain ⟨-, hc, -⟩ := stAt_facts ET off t (by omega)
          obtain ⟨hv, hk⟩ := eStep_spec hc hz
          refine ⟨hv, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact hchk i hi
          · exact hk
  rcases key n le_rfl with h0 | ⟨-, hchk⟩
  · exfalso
    rw [enumRun_iter] at hcnt
    change eCnt (F^[n] 1) = n + 1 at hcnt
    rw [h0] at hcnt
    have hz : eCnt 0 = 0 := by
      unfold eCnt
      simp
    omega
  · exact hchk

theorem enum_sound {ET : Nat → Nat} {G ng n off : Nat}
    (h : Nat.beq (eCnt (enumRun ET G ng n off n 1)) (Nat.succ n) = true)
    (hG : ∀ k < ng, IsP (gk G k)) :
    (∀ i < n, IsP (eCode ET off i) ∧
      perm16 (eCode ET off i) ∈ Submonoid.closure {x | ∃ k < ng, x = perm16 (gk G k)}) ∧
    (∀ i < n, ∀ j < n, eCode ET off i = eCode ET off j → i = j) ∧
    (∀ i < n, ∀ k < ng, ∃ j < n, pmul (eCode ET off i) (gk G k) = eCode ET off j) := by
  obtain ⟨hn, hchk⟩ := enum_checks h
  set C := Submonoid.closure {x | ∃ k < ng, x = perm16 (gk G k)}
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ r, ∀ i < n, eRank (eRec ET (Nat.add off i)) = r →
        IsP (eCode ET off i) ∧ perm16 (eCode ET off i) ∈ C := by
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ih =>
        intro i hi hr
        obtain ⟨-, hroot, htree, -⟩ := hchk i hi
        cases hR : eRoot (eRec ET (Nat.add off i))
        · obtain ⟨hp, hk, hrank, he⟩ := htree hR
          obtain ⟨h1, h2⟩ := ih _ (hr ▸ hrank) _ hp rfl
          rw [he]
          refine ⟨isP_pmul h1 (hG _ hk), ?_⟩
          rw [perm16_pmul h1 (hG _ hk)]
          exact C.mul_mem h2 (Submonoid.subset_closure ⟨_, hk, rfl⟩)
        · rw [hroot hR]
          exact ⟨isP_idP, by rw [perm16_idP]; exact C.one_mem⟩
    exact fun i hi => key _ i hi rfl
  · have hinc : ∀ t, t + 1 < n → eCode ET off t < eCode ET off (t + 1) := by
      intro t ht
      obtain ⟨h1, -⟩ := hchk (t + 1) ht
      rcases h1 with h1 | h1
      · omega
      · rwa [(stAt_facts ET off (t + 1) (by omega)).2.2 t rfl] at h1
    have hlt : ∀ d i, i + d + 1 < n → eCode ET off i < eCode ET off (i + d + 1) := by
      intro d
      induction d with
      | zero => exact fun i hi => hinc i hi
      | succ d ih =>
        intro i hi
        exact Nat.lt_trans (ih i (by omega)) (hinc (i + d + 1) (by omega))
    intro i hi j hj e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · have := hlt (j - i - 1) i (by omega)
      have e' : i + (j - i - 1) + 1 = j := by omega
      rw [e'] at this
      omega
    · have := hlt (i - j - 1) j (by omega)
      have e' : j + (i - j - 1) + 1 = i := by omega
      rw [e'] at this
      omega
  · intro i hi k hk
    obtain ⟨-, -, -, hcl⟩ := hchk i hi
    obtain ⟨h1, h2⟩ := hcl k hk
    exact ⟨_, h1, h2⟩

end CFSG.KS.P16

end
